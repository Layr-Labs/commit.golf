import CommitGolfDepth.Rounds.RoundMachine

/-! Solver-side symbolic rules for the oracle-round interpreter.

These theorems do not modify its semantics or any security certificate. A table is
specified by four word-read facts per index, not by expanding its length. Snapshot
hypotheses concern the common pre-call state, including when outputs alias inputs.
The continuation rules preserve every possible oracle reply, failure and coin path.
Batch rules begin at the ECALL; ordinary rules expose each real nonbatch tick.
Callers must separately charge construction of the table and input buffers and
prove their continuation invariants.
-/

namespace CommitGolfDepth.Rounds.Proofs
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec RiscvZkvm.Rv64
open CommitGolfDepth.Rounds.Batch CommitGolfDepth.Rounds.RoundMachine

/-- A symbolic table uses the real four-word parser at every index. -/
theorem loadDescriptors_formula (state : MachineState) (base : BitVec 64) (count : Nat)
    (table : Nat → Descriptor) (valid : ArrayValid base count)
    (words : ∀ i < count,
      readBuffer state (base.toNat + 32*i) 8 = (table i).kind ∧
      readBuffer state (base.toNat + 32*i + 8) 8 = (table i).source ∧
      readBuffer state (base.toNat + 32*i + 16) 8 = (table i).inputBytes ∧
      readBuffer state (base.toNat + 32*i + 24) 8 = (table i).destination) :
    loadDescriptors state base count = some ((List.range count).map table) := by
  rw [loadDescriptors, ite_eq_left valid]
  congr 1
  apply List.map_congr_left
  intro i member
  obtain ⟨kind, source, inputBytes, destination⟩ := words i (List.mem_range.mp member)
  unfold readDescriptor
  rw [kind, source, inputBytes, destination]

/-- Induction over the index list avoids expanding a large literal table. -/
theorem snapshotAll_map (state : MachineState) (indices : List Nat)
    (table : Nat → Descriptor) (requests : Nat → Request)
    (valid : ∀ i ∈ indices, snapshot state (table i) = some (requests i)) :
    snapshotAll state (indices.map table) = some (indices.map requests) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.map_cons, snapshotAll, valid i (List.mem_cons_self ..)]
      rw [ih (fun j hj => valid j (List.mem_cons_of_mem i hj))]
      rfl

/-- Dispatch a valid batch inside the actual bounded interpreter, with arbitrary
remaining fuel and continuation. Empty batches pay entry cost but zero rounds. -/
theorem executeBatched_batch (image : Image) (state : MachineState) (steps : Nat)
    (coins : Bool) (descriptors : List Descriptor) (requests : List Request)
    (call : isBatchCall image state = true)
    (loaded : loadDescriptors state (state.getReg .x10) (state.getReg .x11).toNat =
      some descriptors)
    (captured : snapshotAll state descriptors = some requests) :
    executeBatched image (steps+1) state coins = (do
      let written ← runFrozenWorld state requests
      let rest ← executeBatched image steps (written.setPC (state.pc + 4)) coins
      pure (charge rest ((quote requests).priced batchFees) requests.length (rounds requests))) := by
  rw [executeBatched, call]
  simp only [ite_true, loaded, captured]

/-- Four word-read invariants and pointwise captures suffice for a complete symbolic
batch step at any admitted count, including zero. Both use the original state. -/
theorem executeBatched_regular (image : Image) (state : MachineState) (steps count : Nat)
    (coins : Bool) (table : Nat → Descriptor) (requests : Nat → Request)
    (call : isBatchCall image state = true)
    (countReg : (state.getReg .x11).toNat = count)
    (valid : ArrayValid (state.getReg .x10) count)
    (words : ∀ i < count,
      readBuffer state ((state.getReg .x10).toNat + 32*i) 8 = (table i).kind ∧
      readBuffer state ((state.getReg .x10).toNat + 32*i + 8) 8 = (table i).source ∧
      readBuffer state ((state.getReg .x10).toNat + 32*i + 16) 8 = (table i).inputBytes ∧
      readBuffer state ((state.getReg .x10).toNat + 32*i + 24) 8 = (table i).destination)
    (captured : ∀ i < count, snapshot state (table i) = some (requests i)) :
    executeBatched image (steps+1) state coins = (do
      let written ← runFrozenWorld state ((List.range count).map requests)
      let rest ← executeBatched image steps (written.setPC (state.pc + 4)) coins
      pure (charge rest (preparationCycles count +
        requestCost oracleCycles ((List.range count).map requests)) count
        (if count = 0 then 0 else 1))) := by
  have loaded := loadDescriptors_formula state (state.getReg .x10) count table valid words
  have snapped := snapshotAll_map state (List.range count) table requests
    (fun i hi => captured i (List.mem_range.mp hi))
  have length : ((List.range count).map requests).length = count := by simp
  have roundCount : rounds ((List.range count).map requests) =
      (if count = 0 then 0 else 1) := by
    cases count <;> simp [rounds]
  rw [executeBatched_batch image state steps coins _ _ call
    (by simpa only [countReg] using loaded) snapped, batch_price, length, roundCount]

private theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

private theorem oracle_run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β) :
    oracle.run (computation >>= continuation) = (do
      let (value, first) ← oracle.run computation
      let (result, second) ← oracle.run (continuation value)
      pure (result, first + second)) := by
  simp only [Oracle.run, simulateQ_bind, WriterT.run_bind, map_eq_bind_pure_comp]
  rfl

/-- The real fixed-oracle runner counts every captured query before the continuation.
This preserves repeated-query correlations and does not resample the oracle. -/
theorem executeBatched_batch_counted (oracle : Oracle) (image : Image)
    (state : MachineState) (steps : Nat) (coins : Bool)
    (descriptors : List Descriptor) (requests : List Request)
    (call : isBatchCall image state = true)
    (loaded : loadDescriptors state (state.getReg .x10) (state.getReg .x11).toNat =
      some descriptors)
    (captured : snapshotAll state descriptors = some requests) :
    oracle.run (executeBatched image (steps+1) state coins) = (do
      let (rest, calls) ← oracle.run (executeBatched image steps
        ((evaluateFrozen oracle state requests).setPC (state.pc+4)) coins)
      pure (charge rest ((quote requests).priced batchFees) requests.length
        (rounds requests), requests.length + calls)) := by
  rw [executeBatched_batch image state steps coins descriptors requests call loaded captured,
    oracle_run_bind, runFrozenWorld_counted]
  simp only [pure_bind]
  rw [oracle_run_bind]
  simp only [oracle_run_pure, pure_bind, Nat.add_zero, bind_assoc]

/-- Componentwise bounds on one execution result. The support-quantified rules below
establish these bounds for every syntactic oracle/coin reply. -/
def Bounds (result : CommitGolfDepth.Rounds.RoundMachine.Execution) (work queries depth : Nat) : Prop :=
  result.result.cycles ≤ work ∧ result.result.oracleCalls ≤ queries ∧
    result.oracleRounds ≤ depth

theorem charge_bounds (result : CommitGolfDepth.Rounds.RoundMachine.Execution) (work queries depth fee calls rounds : Nat)
    (bounded : Bounds result work queries depth) :
    Bounds (charge result fee calls rounds) (fee+work) (calls+queries) (rounds+depth) := by
  rcases bounded with ⟨hw, hq, hd⟩
  exact ⟨Nat.add_le_add_left hw _, Nat.add_le_add_left hq _, Nat.add_le_add_left hd _⟩

/-- Compose a valid batch with a continuation bound for all possible replies. There
is no success assumption that could omit faults, fuel exhaustion or coin paths. -/
theorem executeBatched_batch_bounds (image : Image) (state : MachineState) (steps : Nat)
    (coins : Bool) (descriptors : List Descriptor) (requests : List Request)
    (call : isBatchCall image state = true)
    (loaded : loadDescriptors state (state.getReg .x10) (state.getReg .x11).toNat =
      some descriptors)
    (captured : snapshotAll state descriptors = some requests)
    (work queries depth : Nat)
    (continuation : ∀ written ∈ support (runFrozenWorld state requests),
      ∀ rest ∈ support (executeBatched image steps (written.setPC (state.pc+4)) coins),
        Bounds rest work queries depth)
    (result : CommitGolfDepth.Rounds.RoundMachine.Execution) (reached : result ∈ support
      (executeBatched image (steps+1) state coins)) :
    Bounds result ((quote requests).priced batchFees + work)
      (requests.length+queries) (rounds requests+depth) := by
  rw [executeBatched_batch image state steps coins descriptors requests call loaded captured] at reached
  obtain ⟨written, hw, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
  obtain ⟨rest, hr, final⟩ := (mem_support_bind_iff _ _ _).mp reached
  simp only [support_pure, Set.mem_singleton_iff] at final
  subst result
  exact charge_bounds rest work queries depth _ _ _ (continuation written hw rest hr)

/-- Pointwise binary-tree compression capture. The source and destination may alias
other requests: only this common pre-call state is read. The default rounds track
has 64-byte compression inputs and 32-byte replies. -/
theorem snapshot_compression (state : MachineState) (source destination : BitVec 64)
    (sourceAligned : source.toNat % 8 = 0)
    (destinationAligned : destination.toNat % 8 = 0)
    (sourceFits : rangeValid source 64 = true)
    (destinationFits : rangeValid destination 32 = true) :
    snapshot state ⟨0, source, 64, destination⟩ =
      some ⟨.inl (BitVec.ofNat COMPRESSION_INPUT_LENGTH
        (readBuffer state source.toNat 64).toNat), destination⟩ := by
  simp [snapshot, descriptorState, oracleInput, MachineState.getReg, MachineState.setReg,
    COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sourceAligned, destinationAligned,
    sourceFits, destinationFits]
  rfl

/-- Exact macro work for a compression-only tree level, independent of its inputs
and destinations. This excludes the caller's descriptor/input preparation. -/
theorem compression_quote (indices : List Nat)
    (inputs : Nat → BitVec COMPRESSION_INPUT_LENGTH) (destinations : Nat → BitVec 64) :
    (quote (indices.map fun i => (⟨.inl (inputs i), destinations i⟩ : Request))).priced
      batchFees = 1 + 13 * indices.length := by
  rw [batch_price]
  simp [preparationCycles, requestCost, oracleCycles, COMPRESSION_CYCLES, List.map_map, Function.comp_def]
  omega

/-- Every nonbatch instruction runs through one actual legacy-machine tick. Only
an unfinished tick enters the remaining fuel; HALT and faults return immediately.
A single ordinary oracle call contributes one round, while private coins add none. -/
theorem executeBatched_nonbatch (image : Image) (state : MachineState) (steps : Nat)
    (coins : Bool) (nonbatch : isBatchCall image state = false) :
    executeBatched image (steps+1) state coins = (do
      let tick ← Riscv.execute image 1 state coins
      if tick.exit = .unfinished then do
        let rest ← executeBatched image steps tick.state coins
        pure (charge rest tick.cycles tick.oracleCalls tick.oracleCalls)
      else pure (⟨tick, tick.oracleCalls⟩ : CommitGolfDepth.Rounds.RoundMachine.Execution)) := by
  rw [executeBatched, nonbatch]
  simp only [Bool.false_eq_true, ite_false]

/-- Reuse any deterministic one-tick machine theorem without reducing a whole
batched execution. The terminal branch includes both successful HALT and faults. -/
theorem executeBatched_tick (image : Image) (state : MachineState) (steps : Nat)
    (coins : Bool) (tick : Riscv.Execution)
    (nonbatch : isBatchCall image state = false)
    (oneTick : Riscv.execute image 1 state coins = pure tick) :
    executeBatched image (steps+1) state coins =
      if tick.exit = .unfinished then (do
        let rest ← executeBatched image steps tick.state coins
        pure (charge rest tick.cycles tick.oracleCalls tick.oracleCalls))
      else pure (⟨tick, tick.oracleCalls⟩ : CommitGolfDepth.Rounds.RoundMachine.Execution) := by
  rw [executeBatched_nonbatch image state steps coins nonbatch, oneTick]
  simp only [pure_bind]

/-- The usual setup/loop step: its one-tick theorem has no terminal result yet.
The continuation retains the remaining fuel, including zero fuel. -/
theorem executeBatched_tick_unfinished (image : Image) (state next : MachineState)
    (steps cost calls : Nat) (coins : Bool)
    (nonbatch : isBatchCall image state = false)
    (oneTick : Riscv.execute image 1 state coins = pure ⟨.unfinished, next, cost, calls⟩) :
    executeBatched image (steps+1) state coins = (do
      let rest ← executeBatched image steps next coins
      pure (charge rest cost calls calls)) := by
  rw [executeBatched_tick image state steps coins _ nonbatch oneTick]
  simp only [ite_true]

/-- A terminal one-tick proof does not require or charge any continuation. -/
theorem executeBatched_tick_terminal (image : Image) (state : MachineState)
    (steps : Nat) (coins : Bool) (tick : Riscv.Execution)
    (nonbatch : isBatchCall image state = false)
    (oneTick : Riscv.execute image 1 state coins = pure tick)
    (terminal : tick.exit ≠ .unfinished) :
    executeBatched image (steps+1) state coins =
      pure (⟨tick, tick.oracleCalls⟩ : CommitGolfDepth.Rounds.RoundMachine.Execution) := by
  rw [executeBatched_tick image state steps coins tick nonbatch oneTick, ite_eq_right terminal]

/-- Resource induction for ordinary instructions, including public queries, private
coins, successful HALTs and faults. Tick bounds cover every possible reply. Only
unfinished ticks require a continuation bound; no terminal path is discarded. -/
theorem executeBatched_nonbatch_bounds (image : Image) (state : MachineState) (steps : Nat)
    (coins : Bool) (nonbatch : isBatchCall image state = false)
    (tickWork tickQueries restWork restQueries restDepth : Nat)
    (ticks : ∀ tick ∈ support (Riscv.execute image 1 state coins),
      tick.cycles ≤ tickWork ∧ tick.oracleCalls ≤ tickQueries)
    (continuation : ∀ tick ∈ support (Riscv.execute image 1 state coins),
      tick.exit = .unfinished →
      ∀ rest ∈ support (executeBatched image steps tick.state coins),
        Bounds rest restWork restQueries restDepth)
    (result : CommitGolfDepth.Rounds.RoundMachine.Execution)
    (reached : result ∈ support (executeBatched image (steps+1) state coins)) :
    Bounds result (tickWork+restWork) (tickQueries+restQueries) (tickQueries+restDepth) := by
  rw [executeBatched_nonbatch image state steps coins nonbatch] at reached
  obtain ⟨tick, ht, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
  obtain ⟨hw, hq⟩ := ticks tick ht
  by_cases unfinished : tick.exit = .unfinished
  · simp only [unfinished, ite_true] at reached
    obtain ⟨rest, hr, final⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure, Set.mem_singleton_iff] at final
    subst result
    have bounded := continuation tick ht unfinished rest hr
    rcases bounded with ⟨rw, rq, rd⟩
    exact ⟨Nat.add_le_add hw rw, Nat.add_le_add hq rq, Nat.add_le_add hq rd⟩
  · simp only [unfinished, ite_false, support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨hw.trans (Nat.le_add_right _ _), hq.trans (Nat.le_add_right _ _),
      hq.trans (Nat.le_add_right _ _)⟩

end CommitGolfDepth.Rounds.Proofs
