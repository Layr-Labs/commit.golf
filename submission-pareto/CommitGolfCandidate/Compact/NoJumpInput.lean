import CommitGolfCandidate.Compact.NoJumpPositions
import CommitGolfCandidate.Compact.NoJumpSetup
import CommitGolfCandidate.Compact.NoJumpSubmission
import CommitGolfCandidate.Compact.OpeningInput

/-! Full execution from every trusted opening input. The state follows the
reference nonce/path sequence, with a relocated final PC and fewer cycles. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

def noJumpOpeningResult (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success,noJumpExitState ((openingPositionState^[positions.card]
    (noJumpInitializedState (submission.initialState .opening (trapdoor,positions)))).setPC 5492),
    13+329*positions.card,0⟩

private theorem noJump_input_frame_mem (s : MachineState) (pc : Word) :
    (s.setPC pc).mem=s.mem := rfl

private theorem noJump_input_setup_registers (s : MachineState) :
    (noJumpInitializedState s).getReg .x9=s.getReg .x12 ∧
    (noJumpInitializedState s).getReg .x24=s.getReg .x13 ∧
    (noJumpInitializedState s).getReg .x25=s.getReg .x15 ∧
    (noJumpInitializedState s).getReg .x27=s.getReg .x16 ∧
    (noJumpInitializedState s).getReg .x19=16777216 ∧
    (noJumpInitializedState s).getReg .x18=s.getReg .x12+1073741824 ∧
    (noJumpInitializedState s).getReg .x16=s.getReg .x16 ∧
    (noJumpInitializedState s).mem=s.mem := by
  simpa only [noJumpInitializedState,MachineState.getReg_setPC,noJump_input_frame_mem] using opening_setup_registers s

private theorem noJump_ready_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute noJumpImage (329 * positions.card + (4 + fuel))
      (noJumpInitializedState (submission.initialState .opening (trapdoor, positions))) true =
        pure ⟨.success, (noJumpOpeningResult trapdoor positions).state, 329 * positions.card + 4, 0⟩ := by
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := noJumpInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have small : positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have counter : ready.getReg .x27 = BitVec.ofNat 64 positions.card :=
    (noJump_input_setup_registers initial).2.2.2.1
  have heap : ready.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
    (noJump_input_setup_registers initial).1
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 submission.layout.indices :=
    (noJump_input_setup_registers initial).2.1
  have outputPointer : ready.getReg .x25 = BitVec.ofNat 64 submission.layout.proof :=
    (noJump_input_setup_registers initial).2.2.1
  have leaves : ready.getReg .x19 = 16777216 := (noJump_input_setup_registers initial).2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 (submission.layout.trapdoor + 1073741824) := by
    rw [(noJump_input_setup_registers initial).2.2.2.2.2.1]
    change BitVec.ofNat 64 submission.layout.trapdoor + BitVec.ofNat 64 1073741824 = _
    rw [BitVec.ofNat_add]
  have memory (address : Word) : ready.getMem address = initial.getMem address :=
    congrFun (noJump_input_setup_registers initial).2.2.2.2.2.2.2 address
  have readyPC : ready.pc = if positions.card=0 then 5492 else 4176 := by
    by_cases empty : positions.card=0
    · simp [ready,noJumpInitializedState,MachineState.setPC,initialCount,empty]
    · have nonnoJump : BitVec.ofNat 64 positions.card≠(0 : Word) := by
        intro noJump
        have equal := congrArg BitVec.toNat noJump
        change positions.card%2^64=0 at equal
        rw [Nat.mod_eq_of_lt small] at equal
        omega
      simp [ready,noJumpInitializedState,MachineState.setPC,initialCount,nonnoJump,empty]
      exact nonnoJump
  have counterZero : ready.getReg .x28=0 := by
    have frame (s : MachineState) : (noJumpInitializedState s).getReg .x28=s.getReg .x28 := by rfl
    exact (frame initial).trans (by rfl)
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
    norm_num [submission, CommitGolfCandidate.submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have indexAligned : (ready.getReg .x24).toNat % 8 = 0 := by rw [indexPointer]; decide
  have saltBound : (ready.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES := by rw [salts]; decide
  have saltAligned : (ready.getReg .x18).toNat % 8 = 0 := by rw [salts]; decide
  have heapBound : (ready.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES := by rw [heap]; decide
  have heapAligned : (ready.getReg .x9).toNat % 8 = 0 := by rw [heap]; decide
  have outputBound : (ready.getReg .x25).toNat + 792 * positions.card ≤ MEMORY_BYTES := by
    rw [outputPointer]
    norm_num [submission, CommitGolfCandidate.submission, candidate, layout, trapdoorBytes, MEMORY_BYTES,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have outputAligned : (ready.getReg .x25).toNat % 8 = 0 := by rw [outputPointer]; decide
  change execute noJumpImage (329 * positions.card + (4 + fuel)) ready true = _
  rw [noJump_positions_loop positions.card cardinal ready counter readyPC counterZero indices indexSpace indexAligned
      leaves saltBound saltAligned heapBound heapAligned outputBound outputAligned,
    noJump_exit _ rfl]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  rfl

private theorem noJump_execution_extra (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute noJumpImage (9 + (329 * positions.card + (4 + fuel)))
      (submission.initialState .opening (trapdoor, positions)) true =
        pure (noJumpOpeningResult trapdoor positions) := by
  rw [noJump_setup _ rfl, noJump_ready_execution]
  simp only [pure_bind, Execution.charge, noJumpOpeningResult]
  congr 2
  omega

private theorem run_opening_eq_execute (candidate : Submission)
    (input : Input candidate.sizes .opening) :
    candidate.run .opening input = execute (candidate.image .opening) (candidate.steps .opening)
      (candidate.initialState .opening input) true := rfl

set_option maxRecDepth 4096 in
/-- Every actual opening input succeeds, with exact cycle and query counts.
This includes all position sets and arbitrary serialized trapdoors. -/
theorem noJump_opening_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    noJumpSubmission.run .opening (trapdoor, positions) = pure (noJumpOpeningResult trapdoor positions) := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have steps : submission.steps .opening =
      9 + (329 * positions.card + (4 + (submission.steps .opening - (13 + 329 * positions.card)))) := by
    norm_num [submission, CommitGolfCandidate.submission, candidate, LENGTH, LOG_LENGTH] at cardinal ⊢
    omega
  exact (run_opening_eq_execute noJumpSubmission (trapdoor, positions)).trans
    ((congrArg (fun fuel => execute noJumpImage fuel
      (submission.initialState .opening (trapdoor, positions)) true) steps).trans
        (noJump_execution_extra trapdoor positions _))

end CommitGolfCandidate.Compact
