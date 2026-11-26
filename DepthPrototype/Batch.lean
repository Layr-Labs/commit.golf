import CommitGolf.Riscv

/-! # Bounded prototype: one nonadaptive public-oracle batch

This is a semantic/resource helper, not a new submission interpreter or certificate.
Every request is snapshotted from the same pre-batch machine state. Only then are
the actual public queries issued. Replies are written in descriptor order, so
overlapping output buffers have deterministic last-writer semantics. Every query
still reaches the same fixed compression/permutation oracle, including repeats
and inverse calls. The resource quote keeps primitive costs and explicit batch
bookkeeping separate; the fee parameters are not proposed production prices.

The concrete descriptor-array parser, RISC-V dispatch/fuel, artifact linkage and
whole-program correctness/security/round bounds remain production obligations.
-/

namespace DepthPrototype.Batch

open CommitGolf CommitGolf.Riscv OracleComp OracleSpec RiscvZkvm.Rv64

/-- Four 64-bit descriptor words, matching the existing syscall's four fields. -/
structure Descriptor where
  kind : BitVec 64
  source : BitVec 64
  inputBytes : BitVec 64
  destination : BitVec 64
  deriving DecidableEq

/-- The query contains the input bytes themselves, not an address to reread later. -/
structure Request where
  query : PublicSpec.Domain
  destination : BitVec 64
  deriving DecidableEq

def descriptorState (state : MachineState) (descriptor : Descriptor) : MachineState :=
  let state := state.setReg .x10 descriptor.source
  let state := state.setReg .x11 descriptor.inputBytes
  let state := state.setReg .x12 descriptor.destination
  state.setReg .x13 descriptor.kind

/-- Reuse the real machine's width, kind, alignment and address checks. -/
def snapshot (state : MachineState) (descriptor : Descriptor) : Option Request := do
  let query ← oracleInput (descriptorState state descriptor)
  return ⟨query, descriptor.destination⟩

/-- Crucially, recursion keeps `state`, rather than a state modified by earlier replies. -/
def snapshotAll (state : MachineState) : List Descriptor → Option (List Request)
  | [] => some []
  | descriptor :: descriptors => do
      let request ← snapshot state descriptor
      let requests ← snapshotAll state descriptors
      return request :: requests

theorem snapshotAll_length (state : MachineState) (descriptors : List Descriptor)
    (requests : List Request) (valid : snapshotAll state descriptors = some requests) :
    requests.length = descriptors.length := by
  induction descriptors generalizing requests with
  | nil =>
      simp only [snapshotAll, Option.some.injEq] at valid
      subst requests
      rfl
  | cons descriptor descriptors ih =>
      cases first : snapshot state descriptor with
      | none => simp [snapshotAll, first] at valid
      | some request =>
          cases rest : snapshotAll state descriptors with
          | none => simp [snapshotAll, first, rest] at valid
          | some tail =>
              simp only [snapshotAll, first, rest] at valid
              change some (request :: tail) = some requests at valid
              have valid := Option.some.inj valid
              subst requests
              simp only [List.length_cons, ih tail rest]

/-- Reply writes preserve PC here. The whole batch advances PC exactly once. -/
def writeReply (state : MachineState) (request : Request)
    (answer : PublicSpec.Range request.query) : MachineState :=
  { writeOracleAnswer state request.destination request.query answer with pc := state.pc }

theorem writeReply_pc (state : MachineState) (request : Request)
    (answer : PublicSpec.Range request.query) :
    (writeReply state request answer).pc = state.pc := rfl

/-- The writeback bridge uses exactly the existing machine's reply bytes. -/
theorem writeReply_memory (state : MachineState) (request : Request)
    (answer : PublicSpec.Range request.query) :
    (writeReply state request answer).mem =
      (writeOracleAnswer state request.destination request.query answer).mem := rfl

/-- Fixed-oracle evaluation of the captured requests, with ordered writeback. -/
def evaluateFrozen (oracle : Oracle) (state : MachineState) : List Request → MachineState
  | [] => state
  | request :: requests =>
      evaluateFrozen oracle
        (writeReply state request (oracle.answer (m := Id) request.query)) requests

theorem evaluateFrozen_pc (oracle : Oracle) (state : MachineState) (requests : List Request) :
    (evaluateFrozen oracle state requests).pc = state.pc := by
  induction requests generalizing state with
  | nil => rfl
  | cons request requests ih =>
      rw [evaluateFrozen, ih, writeReply_pc]

/-- The actual oracle program: no request is reread from modified memory. -/
def runFrozen (state : MachineState) : List Request → OracleComp PublicSpec MachineState
  | [] => pure state
  | request :: requests => do
      let answer ← (PublicSpec.query request.query : OracleComp PublicSpec _)
      runFrozen (writeReply state request answer) requests

/-- A weighted oracle runner, used only to prove this helper's actual calls/costs. -/
def evalWithCost (oracle : Oracle) (price : PublicSpec.Domain → Nat) {α : Type}
    (computation : OracleComp PublicSpec α) : α × Nat :=
  (simulateQ ((oracle.answer (m := Id)).withAddCost price) computation).run

theorem evalWithCost_pure (oracle : Oracle) (price : PublicSpec.Domain → Nat)
    {α : Type} (value : α) :
    evalWithCost oracle price (pure value) = (value, 0) := by
  simp [evalWithCost]
  rfl

theorem evalWithCost_bind (oracle : Oracle) (price : PublicSpec.Domain → Nat)
    {α β : Type} (computation : OracleComp PublicSpec α)
    (continuation : α → OracleComp PublicSpec β) :
    evalWithCost oracle price (computation >>= continuation) =
      let (value, first) := evalWithCost oracle price computation
      let (result, second) := evalWithCost oracle price (continuation value)
      (result, first + second) := by
  simp only [evalWithCost, simulateQ_bind, WriterT.run_bind]
  rfl

theorem evalWithCost_query (oracle : Oracle) (price : PublicSpec.Domain → Nat)
    (query : PublicSpec.Domain) :
    evalWithCost oracle price (PublicSpec.query query : OracleComp PublicSpec _) =
      (oracle.answer (m := Id) query, price query) := by
  rcases query with input | input
  · simp [evalWithCost, Oracle.answer, QueryImpl.withAddCost, QueryImpl.withCost]
    rfl
  · rcases input with input | input <;>
      simp [evalWithCost, Oracle.answer, QueryImpl.withAddCost, QueryImpl.withCost] <;> rfl

theorem evalWithCost_query_bind (oracle : Oracle) (price : PublicSpec.Domain → Nat)
    {α : Type} (query : PublicSpec.Domain)
    (continuation : PublicSpec.Range query → OracleComp PublicSpec α) :
    evalWithCost oracle price ((PublicSpec.query query : OracleComp PublicSpec _) >>= continuation) =
      let (result, rest) := evalWithCost oracle price (continuation (oracle.answer (m := Id) query))
      (result, price query + rest) := by
  rw [evalWithCost_bind, evalWithCost_query]

def requestCost (price : PublicSpec.Domain → Nat) (requests : List Request) : Nat :=
  (requests.map fun request => price request.query).sum

/-- Refinement and exact cost accounting hold for every realization of the oracle. -/
theorem runFrozen_refines (oracle : Oracle) (price : PublicSpec.Domain → Nat)
    (state : MachineState) (requests : List Request) :
    evalWithCost oracle price (runFrozen state requests) =
      (evaluateFrozen oracle state requests, requestCost price requests) := by
  induction requests generalizing state with
  | nil => simp [runFrozen, evaluateFrozen, evalWithCost_pure, requestCost]
  | cons request requests ih =>
      rw [runFrozen, evalWithCost_query_bind, ih]
      rfl

/-- Repeated queries cost repeatedly; a batch of `k` requests consumes `k`, not one. -/
theorem runFrozen_query_count (oracle : Oracle) (state : MachineState)
    (requests : List Request) :
    oracle.eval (runFrozen state requests) =
      (evaluateFrozen oracle state requests, requests.length) := by
  change evalWithCost oracle (fun _ => 1) _ = _
  rw [runFrozen_refines]
  simp [requestCost]

/-- Primitive work is the sum of the existing track's per-query prices. -/
theorem runFrozen_primitive_cycles (oracle : Oracle) (state : MachineState)
    (requests : List Request) :
    evalWithCost oracle oracleCycles (runFrozen state requests) =
      (evaluateFrozen oracle state requests, requestCost oracleCycles requests) :=
  runFrozen_refines oracle oracleCycles state requests

/-- Inverse calls use the same permutation as forward calls; no batch resampling occurs. -/
theorem forward_inverse_consistent (oracle : Oracle) (input : BitVec PERMUTATION_WIDTH) :
    oracle.answer (m := Id) (.inr (.inr (oracle.permutation input))) = input := by
  change oracle.permutation.symm (oracle.permutation input) = input
  exact oracle.permutation.symm_apply_apply input

def rounds (requests : List Request) : Nat := if requests.isEmpty then 0 else 1

@[simp] theorem rounds_nil : rounds [] = 0 := rfl
@[simp] theorem rounds_cons (request : Request) (requests : List Request) :
    rounds (request :: requests) = 1 := rfl

/-- Fees expose fixed macro bookkeeping; they are parameters, not hardware timings. -/
structure Fees where
  entry : Nat
  descriptorWord : Nat
  requestBookkeeping : Nat

structure Quote where
  publicCalls : Nat
  primitiveCycles : Nat
  descriptorWords : Nat
  bookkeepingSteps : Nat
  oracleRounds : Nat

def quote (requests : List Request) : Quote :=
  ⟨requests.length, requestCost oracleCycles requests,
    4 * requests.length, requests.length, rounds requests⟩

def Quote.priced (fees : Fees) (cost : Quote) : Nat :=
  cost.primitiveCycles + fees.entry + fees.descriptorWord * cost.descriptorWords +
    fees.requestBookkeeping * cost.bookkeepingSteps

/-- Empty batches still enter the macro, but make no public call or oracle round. -/
theorem quote_empty (fees : Fees) :
    (quote []).publicCalls = 0 ∧ (quote []).oracleRounds = 0 ∧
      (quote []).priced fees = fees.entry := by
  simp [quote, requestCost, Quote.priced]

/-- Validation precedes every query. All input snapshots therefore precede all writes. -/
def runBatch (state : MachineState) (descriptors : List Descriptor) :
    OracleComp PublicSpec (Option MachineState) :=
  match snapshotAll state descriptors with
  | none => pure none
  | some requests => do
      let final ← runFrozen state requests
      return some (final.setPC (state.pc + 4))

theorem runBatch_invalid (oracle : Oracle) (state : MachineState)
    (descriptors : List Descriptor) (invalid : snapshotAll state descriptors = none) :
    oracle.eval (runBatch state descriptors) = (none, 0) := by
  simp only [runBatch, invalid]
  exact evalWithCost_pure oracle (fun _ => 1) none

/-- One PC advance and the unchanged actual public-query count of the frozen list. -/
theorem runBatch_refines (oracle : Oracle) (state : MachineState)
    (descriptors : List Descriptor) (requests : List Request)
    (valid : snapshotAll state descriptors = some requests) :
    oracle.eval (runBatch state descriptors) =
      (some ((evaluateFrozen oracle state requests).setPC (state.pc + 4)), descriptors.length) := by
  change evalWithCost oracle (fun _ => 1) _ = _
  rw [runBatch, valid, evalWithCost_bind, runFrozen_refines]
  dsimp only
  rw [evalWithCost_pure]
  simp only [Nat.add_zero]
  congr 1
  simpa [requestCost] using snapshotAll_length state descriptors requests valid

end DepthPrototype.Batch
