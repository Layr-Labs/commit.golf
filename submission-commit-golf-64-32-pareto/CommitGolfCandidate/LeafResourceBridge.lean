import CommitGolfCandidate.Resources
import CommitGolfCandidate.LeafRefinement
import CommitGolfCandidate.HidingLeaf
import CommitGolfCandidate.HidingQueries

/-! # Resource bounds for the actual salted leaf

The security reduction below uses the same public-query syntax as the candidate resource program.
Its structural budget follows from VCVio's completed-path bound through the existing World-support
bridge, whose reply types are inhabited. Equality of final values alone would not transfer costs.

The separate machine theorem covers the checker image from PC 4444 through its return to 4196.
Its 159 abstract cycles include the loop and return, but exclude caller salt/input preparation and
the continuation. The 103-step segment intentionally ends `unfinished` at that instruction boundary;
it is not a full commitment, opening or checker runtime, termination, or security theorem.
-/

namespace CommitGolfCandidate.ResourceBridge
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- The software expansion has the same queries, replies and continuation as the existing hiding
program, not merely the same answer under one deterministic handler. -/
theorem hashWorld_eq (salt : Digest) (input : List Digest) :
    Resources.hashWorld salt input = hashBlocks input salt := by
  induction input generalizing salt with
  | nil => rfl
  | cons block rest ih =>
    erw [Resources.hashWorld_cons]
    simp only [hashBlocks]
    congr 1
    funext answer
    exact ih answer

theorem leafWorld_eq (salt : Digest) (value : Entry) :
    Resources.leafWorld (salt, value) =
      hashBlocks ((List.range 8).map fun i => value.extractLsb' (256 * i) 256) salt := by
  erw [Resources.leafWorld_eq_hashWorld, hashWorld_eq]
  rfl

/-- Completed-path counting suffices here because every World reply/continuation has support;
`public_query_bound_of_counted_support` proves that availability step for this concrete World. -/
theorem leaf_public_query_bound (salt : Digest) (value : Entry) :
    PublicQueryBound
      (hashBlocks ((List.range 8).map fun i => value.extractLsb' (256 * i) 256) salt) 8 := by
  rw [← leafWorld_eq]
  apply public_query_bound_of_counted_support
  intro result reached
  have bound := Resources.leafWorld_bound (salt, value)
  exact bound result reached

theorem referenceLeaf_eq (compress : Compression) (salt : Digest) (value : Entry) :
    Resources.referenceLeaf compress (salt, value) = leafDigest compress salt value := rfl

/-- Exact instruction/cycle/public-call decomposition, retaining arbitrary continuation fuel. -/
theorem check_leaf_subroutine_cost
    (state : MachineState) (pc : state.pc = 4444) (link : state.getReg .x1 = 4196)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (103 + fuel) state allowCoins =
      (do let finished ← checkLeafLoop (checkLeafPrepared state) 8
          let result ← execute (submission.image .check) fuel (finished.setPC 4196) allowCoins
          return result.charge 159 8) :=
  check_leaf_subroutine state pc link scratch sourceValid fuel allowCoins

private theorem leaf_loop_run (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (checkLeafLoop state count) =
      pure (checkEvaluation oracle (checkLeafLoop state count)) := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, oracle_run_pure, check_evaluation_pure]
  | succ count ih =>
    simp only [checkLeafLoop, oracle_run_public_bind, check_evaluation_public_bind]
    rw [ih]
    simp only [pure_bind]

private theorem leaf_loop_calls (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (checkLeafLoop state count)).2 = count := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, check_evaluation_pure]
  | succ count ih =>
    simp only [checkLeafLoop, check_evaluation_public_bind]
    rw [ih]
    omega

/-- One actual checker segment has the resource program's digest and eight counted public calls.
All input/scratch separation and access-validity premises are retained. Stopping immediately after
return exposes `unfinished`; the caller and its continuation still need their own machine proofs. -/
theorem check_leaf_segment
    (oracle : Oracle) (state : MachineState) (address : Nat) (salt : Digest) (value : Entry)
    (pc : state.pc = 4444) (link : state.getReg .x1 = 4196)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 320 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state 256 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32*i) 32 = value.extractLsb' (256*i) 256) :
    let initialized := checkLeafPrepared state
    let finished := (checkEvaluation oracle (checkLeafLoop initialized 8)).1
    oracle.run (execute (submission.image .check) 103 state false) =
        pure (({ exit := .unfinished, state := finished.setPC 4196,
                 cycles := 159, oracleCalls := 8 } : Execution), 8) ∧
      readBuffer (finished.setPC 4196) 256 32 = Resources.referenceLeaf oracle.compression (salt, value) ∧
      oracle.run (Resources.leafWorld (salt, value)) =
        pure (Resources.referenceLeaf oracle.compression (salt, value), 8) := by
  dsimp only
  let initialized := checkLeafPrepared state
  have initScratch : initialized.getReg .x21 = 256 := by
    rw [checkLeafPrepared_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact scratch
  have initPointer : initialized.getReg .x8 = BitVec.ofNat 64 address := by
    rw [checkLeafPrepared_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact pointer
  have initSalt : readBuffer initialized 256 32 = salt := initial
  have initData : ∀ i < 8,
      readBuffer initialized (address + 32*i) 32 = value.extractLsb' (256*i) 256 := data
  refine ⟨?_, ?_, Resources.leafWorld_run oracle (salt, value)⟩
  · have execution := check_leaf_subroutine_cost state pc link scratch sourceValid 0 false
    simp only [Nat.add_zero] at execution
    have zero (image : Image) (next : MachineState) :
        execute image 0 next false =
          pure ({ exit := .unfinished, state := next, cycles := 0, oracleCalls := 0 } : Execution) := rfl
    rw [execution]
    simp only [zero]
    rw [oracle_run_bind, leaf_loop_run]
    simp only [oracle_run_pure, pure_bind, Execution.charge, leaf_loop_calls, Nat.add_zero]
  · have readPC (next : MachineState) :
        readBuffer (next.setPC 4196) 256 32 = readBuffer next 256 32 := rfl
    rw [readPC, referenceLeaf_eq]
    exact check_leaf_digest oracle initialized address salt value initScratch initPointer
      aligned above bounded initSalt initData

end CommitGolfCandidate.ResourceBridge
