import CommitGolfCandidate.FastOpeningPositions
import CommitGolfCandidate.FastOpeningSetup
import CommitGolfCandidate.FastOpeningSubmission
import CommitGolfCandidate.OpeningInput

/-! Full execution from every trusted opening input. The state follows the
reference nonce/path sequence, with a relocated final PC and fewer cycles. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def fastOpeningResult (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success,fastExitState ((openingPositionState^[positions.card]
    (fastInitializedState (submission.initialState .opening (trapdoor,positions)))).setPC 5604),
    13+355*positions.card,0⟩

private theorem fast_input_frame_mem (s : MachineState) (pc : Word) :
    (s.setPC pc).mem=s.mem := rfl

private theorem fast_input_setup_registers (s : MachineState) :
    (fastInitializedState s).getReg .x9=s.getReg .x12 ∧
    (fastInitializedState s).getReg .x24=s.getReg .x13 ∧
    (fastInitializedState s).getReg .x25=s.getReg .x15 ∧
    (fastInitializedState s).getReg .x27=s.getReg .x16 ∧
    (fastInitializedState s).getReg .x19=16777216 ∧
    (fastInitializedState s).getReg .x18=s.getReg .x12+1073741824 ∧
    (fastInitializedState s).getReg .x16=s.getReg .x16 ∧
    (fastInitializedState s).mem=s.mem := by
  simpa only [fastInitializedState,MachineState.getReg_setPC,fast_input_frame_mem] using opening_setup_registers s

private theorem fast_ready_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute fastImage (355 * positions.card + (4 + fuel))
      (fastInitializedState (submission.initialState .opening (trapdoor, positions))) true =
        pure ⟨.success, (fastOpeningResult trapdoor positions).state, 355 * positions.card + 4, 0⟩ := by
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := fastInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have small : positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have counter : ready.getReg .x27 = BitVec.ofNat 64 positions.card :=
    (fast_input_setup_registers initial).2.2.2.1
  have heap : ready.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
    (fast_input_setup_registers initial).1
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 submission.layout.indices :=
    (fast_input_setup_registers initial).2.1
  have outputPointer : ready.getReg .x25 = BitVec.ofNat 64 submission.layout.proof :=
    (fast_input_setup_registers initial).2.2.1
  have leaves : ready.getReg .x19 = 16777216 := (fast_input_setup_registers initial).2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 (submission.layout.trapdoor + 1073741824) := by
    rw [(fast_input_setup_registers initial).2.2.2.2.2.1]
    change BitVec.ofNat 64 submission.layout.trapdoor + BitVec.ofNat 64 1073741824 = _
    rw [BitVec.ofNat_add]
  have memory (address : Word) : ready.getMem address = initial.getMem address :=
    congrFun (fast_input_setup_registers initial).2.2.2.2.2.2.2 address
  have readyPC : ready.pc = if positions.card=0 then 5604 else 4176 := by
    by_cases empty : positions.card=0
    · simp [ready,fastInitializedState,MachineState.setPC,initialCount,empty]
    · have nonzero : BitVec.ofNat 64 positions.card≠(0 : Word) := by
        intro zero
        have equal := congrArg BitVec.toNat zero
        change positions.card%2^64=0 at equal
        rw [Nat.mod_eq_of_lt small] at equal
        omega
      simp [ready,fastInitializedState,MachineState.setPC,initialCount,nonzero,empty]
      exact nonzero
  have indices : ∀ offset < positions.card,
      (ready.getMem (ready.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
    intro offset bounded
    rw [indexPointer, ← BitVec.ofNat_add, memory, opening_input_index trapdoor positions offset bounded]
    have indexBound : ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val < 2 ^ 24 :=
      ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact indexBound
  have indexSpace : (ready.getReg .x24).toNat + 8 * positions.card ≤ (ready.getReg .x25).toNat := by
    rw [indexPointer, outputPointer]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have indexAligned : (ready.getReg .x24).toNat % 8 = 0 := by rw [indexPointer]; decide
  have saltBound : (ready.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES := by rw [salts]; decide
  have saltAligned : (ready.getReg .x18).toNat % 8 = 0 := by rw [salts]; decide
  have heapBound : (ready.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES := by rw [heap]; decide
  have heapAligned : (ready.getReg .x9).toNat % 8 = 0 := by rw [heap]; decide
  have outputBound : (ready.getReg .x25).toNat + 800 * positions.card ≤ MEMORY_BYTES := by
    rw [outputPointer]
    norm_num [submission, candidate, layout, trapdoorBytes, MEMORY_BYTES,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have outputAligned : (ready.getReg .x25).toNat % 8 = 0 := by rw [outputPointer]; decide
  change execute fastImage (355 * positions.card + (4 + fuel)) ready true = _
  rw [fast_positions_loop positions.card cardinal ready counter readyPC indices indexSpace indexAligned
      leaves saltBound saltAligned heapBound heapAligned outputBound outputAligned,
    fast_exit _ rfl]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  rfl

private theorem fast_execution_extra (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute fastImage (9 + (355 * positions.card + (4 + fuel)))
      (submission.initialState .opening (trapdoor, positions)) true =
        pure (fastOpeningResult trapdoor positions) := by
  rw [fast_setup _ rfl, fast_ready_execution]
  simp only [pure_bind, Execution.charge, fastOpeningResult]
  congr 2
  omega

private theorem run_opening_eq_execute (candidate : Submission)
    (input : Input candidate.sizes .opening) :
    candidate.run .opening input = execute (candidate.image .opening) (candidate.steps .opening)
      (candidate.initialState .opening input) true := rfl

set_option maxRecDepth 4096 in
/-- Every actual opening input succeeds, with exact cycle and query counts.
This includes all position sets and arbitrary serialized trapdoors. -/
theorem fast_opening_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    fastSubmission.run .opening (trapdoor, positions) = pure (fastOpeningResult trapdoor positions) := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have steps : submission.steps .opening =
      9 + (355 * positions.card + (4 + (submission.steps .opening - (13 + 355 * positions.card)))) := by
    norm_num [submission, candidate, LENGTH, LOG_LENGTH] at cardinal ⊢
    omega
  exact (run_opening_eq_execute fastSubmission (trapdoor, positions)).trans
    ((congrArg (fun fuel => execute fastImage fuel
      (submission.initialState .opening (trapdoor, positions)) true) steps).trans
        (fast_execution_extra trapdoor positions _))

end CommitGolfCandidate
