import DepthPrototype.Batch

/-! # Isolated RISC-V batch-instruction prototype

The new selector is ECALL with t0=3; a0 points to four-word descriptors and a1 is
their count. Count/address checks precede list allocation. All descriptors and
query inputs refer to the same pre-call state. Only then are public queries made.

The fixed prototype price is one entry cycle, four descriptor-word cycles and
one bookkeeping cycle per request, plus the existing primitive prices. These are
new benchmark macro prices, not an instruction-level implementation/runtime proof.
Preparation by a caller is not performed by this macro and is not free program work.

Legacy mode delegates exactly to the existing interpreter. Batched mode is a new
semantics, not an assertion that every old program remains equivalent. This file
does not change the live interpreter, artifacts, certificate or security games.
-/

namespace DepthPrototype.BatchMachine

open CommitGolf CommitGolf.Riscv OracleComp OracleSpec RiscvZkvm.Rv64
open DepthPrototype.Batch

def MAX_BATCH : Nat := LENGTH

theorem max_batch_positive : 0 < MAX_BATCH := by decide

/-- Nat arithmetic here prevents address multiplication/addition from wrapping. -/
def ArrayValid (base : BitVec 64) (count : Nat) : Prop :=
  count ≤ MAX_BATCH ∧ base.toNat % 8 = 0 ∧ base.toNat + 32 * count ≤ MEMORY_BYTES

instance (base : BitVec 64) (count : Nat) : Decidable (ArrayValid base count) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def readDescriptor (state : MachineState) (address : Nat) : Descriptor :=
  ⟨readBuffer state address 8, readBuffer state (address + 8) 8,
    readBuffer state (address + 16) 8, readBuffer state (address + 24) 8⟩

def loadDescriptors (state : MachineState) (base : BitVec 64) (count : Nat) :
    Option (List Descriptor) :=
  if ArrayValid base count then
    some ((List.range count).map fun i => readDescriptor state (base.toNat + 32 * i))
  else none

theorem loadDescriptors_too_large (state : MachineState) (base : BitVec 64) (count : Nat)
    (large : MAX_BATCH < count) : loadDescriptors state base count = none := by
  apply if_neg
  intro valid
  exact Nat.not_le_of_gt large valid.1

theorem loadDescriptors_invalid (state : MachineState) (base : BitVec 64) (count : Nat)
    (invalid : ¬ ArrayValid base count) : loadDescriptors state base count = none :=
  if_neg invalid

theorem loadDescriptors_length (state : MachineState) (base : BitVec 64) (count : Nat)
    (descriptors : List Descriptor) (loaded : loadDescriptors state base count = some descriptors) :
    descriptors.length = count ∧ ArrayValid base count := by
  unfold loadDescriptors at loaded
  split at loaded
  · rename_i valid
    simp only [Option.some.injEq] at loaded
    subst descriptors
    exact ⟨by simp, valid⟩
  · simp at loaded

/-- Every loaded descriptor word is aligned, in memory, and below 2^64. -/
theorem descriptor_word_in_bounds (base : BitVec 64) (count i offset : Nat)
    (valid : ArrayValid base count) (inside : i < count)
    (offsetBound : offset ≤ 24) (offsetAligned : offset % 8 = 0) :
    (base.toNat + 32 * i + offset) % 8 = 0 ∧
      base.toNat + 32 * i + offset + 8 ≤ MEMORY_BYTES ∧
      base.toNat + 32 * i + offset + 8 < 2 ^ 64 := by
  rcases valid with ⟨_, aligned, bounded⟩
  have addressBound : base.toNat + 32 * i + offset + 8 ≤ MEMORY_BYTES := by omega
  have ceiling : MEMORY_BYTES < 2 ^ 64 := by decide
  refine ⟨?_, addressBound, lt_of_le_of_lt addressBound ceiling⟩
  omega

/-- Actual World queries, so the security-game runner independently counts all calls. -/
def runFrozenWorld (state : MachineState) : List Request → OracleComp World MachineState
  | [] => pure state
  | request :: requests => do
      let answer ← (liftM (World.query (.inr request.query)) : OracleComp World _)
      runFrozenWorld (writeReply state request answer) requests

private theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

private theorem oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β) :
    oracle.run (computation >>= continuation) =
      (do let (value, first) ← oracle.run computation
          let (result, second) ← oracle.run (continuation value)
          return (result, first + second)) := by
  simp only [Oracle.run, simulateQ_bind, WriterT.run_bind, map_eq_bind_pure_comp]
  rfl

private theorem oracle_run_public (oracle : Oracle) (query : PublicSpec.Domain) :
    oracle.run (liftM (World.query (.inr query)) : OracleComp World (PublicSpec.Range query)) =
      pure (oracle.answer (m := Id) query, 1) := by
  rcases query with input | input
  · simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
      QueryImpl.withAddCost, QueryImpl.withCost]
    rfl
  · rcases input with input | input <;>
      simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
        QueryImpl.withAddCost, QueryImpl.withCost] <;> rfl

/-- The independent World counter agrees with the batch's proposed k-call counter. -/
theorem runFrozenWorld_counted (oracle : Oracle) (state : MachineState)
    (requests : List Request) :
    oracle.run (runFrozenWorld state requests) =
      pure (evaluateFrozen oracle state requests, requests.length) := by
  induction requests generalizing state with
  | nil => exact oracle_run_pure oracle state
  | cons request requests ih =>
      rw [runFrozenWorld, oracle_run_bind, oracle_run_public]
      simp only [pure_bind]
      rw [ih]
      simp only [pure_bind, evaluateFrozen, List.length_cons, Nat.add_comm]

def prototypeFees : Fees := ⟨1, 1, 1⟩

/-- Explicit price of descriptor decoding/validation, without any oracle calls. -/
def preparationCycles (count : Nat) : Nat := 1 + 5 * count

theorem batch_price (requests : List Request) :
    (quote requests).priced prototypeFees =
      preparationCycles requests.length + requestCost oracleCycles requests := by
  simp only [quote, Quote.priced, prototypeFees, preparationCycles]
  omega

structure Execution where
  result : Riscv.Execution
  oracleRounds : Nat

def charge (execution : Execution) (cycles calls rounds : Nat) : Execution :=
  ⟨execution.result.charge cycles calls, rounds + execution.oracleRounds⟩

def failed (state : MachineState) (cycles : Nat) : Execution :=
  ⟨⟨.failure, state, cycles, 0⟩, 0⟩

/-- Structural decoding avoids assuming decidable equality for arbitrary instructions. -/
def isBatchCall (image : Image) (state : MachineState) : Bool :=
  match fetch image state with
  | some (.base .ECALL) => state.getReg .x5 == 3
  | _ => false

/-- One batch consumes one instruction of fuel, but k public queries and their full work. -/
def executeBatched (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool := true) : OracleComp World Execution :=
  match steps with
  | 0 => pure ⟨⟨.unfinished, state, 0, 0⟩, 0⟩
  | steps + 1 =>
      if isBatchCall image state then
        let count := (state.getReg .x11).toNat
        match loadDescriptors state (state.getReg .x10) count with
        | none => pure (failed state 1)
        | some descriptors =>
            match snapshotAll state descriptors with
            | none => pure (failed state (preparationCycles count))
            | some requests => do
                let written ← runFrozenWorld state requests
                let rest ← executeBatched image steps (written.setPC (state.pc + 4)) allowCoins
                return charge rest ((quote requests).priced prototypeFees)
                  requests.length (rounds requests)
      else do
        let tick ← Riscv.execute image 1 state allowCoins
        if tick.exit = .unfinished then
          let rest ← executeBatched image steps tick.state allowCoins
          return charge rest tick.cycles tick.oracleCalls tick.oracleCalls
        else return ⟨tick, tick.oracleCalls⟩

inductive Mode where
  | legacy | batched
  deriving DecidableEq

/-- The mode is explicit data. It is not inferred from a claim or a security proof. -/
def execute (mode : Mode) (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool := true) : OracleComp World Execution :=
  match mode with
  | .legacy =>
      (fun result => (⟨result, result.oracleCalls⟩ : Execution)) <$>
        Riscv.execute image steps state allowCoins
  | .batched => executeBatched image steps state allowCoins

/-- Exact whole-computation compatibility in legacy mode, for all inputs and coins. -/
theorem execute_legacy_projection (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool) :
    (fun execution => execution.result) <$> execute .legacy image steps state allowCoins =
      Riscv.execute image steps state allowCoins := by
  simp only [execute, Functor.map_map]
  exact id_map _

theorem execute_legacy_rounds (image : Image) (steps : Nat) (state : MachineState)
    (allowCoins : Bool) :
    (fun execution => execution.oracleRounds) <$> execute .legacy image steps state allowCoins =
      (fun result => result.oracleCalls) <$> Riscv.execute image steps state allowCoins := by
  simp only [execute, Functor.map_map]

end DepthPrototype.BatchMachine
