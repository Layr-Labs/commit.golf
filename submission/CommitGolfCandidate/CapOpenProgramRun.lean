import CommitGolfCandidate.CapOpenResult
import CommitGolfCandidate.CapOpenEmpty

/-! Instantiate the complete opening execution with its actual declared fuel.
Both empty and nonempty requests run the experimental image and retain the
real return state; this is independent of honest commitment semantics. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem opening_run_eq (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    program.run .opening (trapdoor, positions) =
      execute (program.image .opening) (program.steps .opening)
        (program.initialState .opening (trapdoor, positions)) true := rfl

def capOpenInstructionCount (positions : Positions) : Nat :=
  29+278*positions.card+1272+2+
    capDfsInstructionTotal false (capOpenRequestedMarks positions) 510 (.visit 1)+4

theorem cap_open_program_fuel (positions : Positions) :
    capOpenInstructionCount positions ≤ capProgram.steps .opening := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have traversal := cap_dfs_instruction_total_bound false
    (capOpenRequestedMarks positions) 510 (.visit 1)
  change 29+278*positions.card+1272+2+
    capDfsInstructionTotal false (capOpenRequestedMarks positions) 510 (.visit 1)+4 ≤
      13421773824
  norm_num [LENGTH, LOG_LENGTH] at cardinal
  omega

theorem cap_open_nonempty_program_run
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    capProgram.run .opening (trapdoor, positions) =
      pure (capOpenNonemptyResult trapdoor positions) := by
  have fuel := cap_open_program_fuel positions
  have execution := cap_open_loaded_execution trapdoor positions positive
    (capProgram.steps .opening-capOpenInstructionCount positions) true
  have count : 29+278*positions.card+1272+2+
      capDfsInstructionTotal false (capOpenRequestedMarks positions) 510 (.visit 1)+4+
      (capProgram.steps .opening-capOpenInstructionCount positions) =
        capProgram.steps .opening := by
    change capOpenInstructionCount positions+
      (capProgram.steps .opening-capOpenInstructionCount positions) = _
    omega
  rw [count, cap_open_dfs_run_pure] at execution
  rw [opening_run_eq]
  simpa only [pure_bind, capOpenNonemptyResult, capOpenFinalState] using execution

def capOpenEmptyResult
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : Execution :=
  ⟨.success, capOpenExitState
    (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions))), 33, 0⟩

theorem cap_open_empty_program_run
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (empty : positions.card = 0) :
    capProgram.run .opening (trapdoor, positions) =
      pure (capOpenEmptyResult trapdoor positions) := by
  have pc : (capProgram.initialState .opening (trapdoor, positions)).pc = 4096 := rfl
  have counter : (capProgram.initialState .opening (trapdoor, positions)).getReg .x16 = 0 := by
    change BitVec.ofNat 64 positions.card = 0
    rw [empty]
    rfl
  have execution := cap_open_empty_execute _ pc counter
    (capProgram.steps .opening-33) true
  have count : 33+(capProgram.steps .opening-33) = capProgram.steps .opening := by
    have enough : 33 ≤ capProgram.steps .opening := by decide
    omega
  rw [count] at execution
  rw [opening_run_eq]
  simpa only [capOpenEmptyResult] using execution

theorem cap_open_nonempty_scheme_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    capProgram.scheme.opening trapdoor positions =
      pure (capOpenLoadedBytes trapdoor positions) := by
  change capProgram.readProof <$> capProgram.run .opening (trapdoor, positions) = _
  rw [cap_open_nonempty_program_run trapdoor positions positive]
  simp only [map_pure, cap_open_nonempty_read_proof trapdoor positions positive]

theorem cap_open_empty_scheme_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (empty : positions.card = 0) :
    capProgram.scheme.opening trapdoor positions = pure [] := by
  change capProgram.readProof <$> capProgram.run .opening (trapdoor, positions) = _
  rw [cap_open_empty_program_run trapdoor positions empty, map_pure]
  have length : ((capOpenEmptyResult trapdoor positions).state.getReg .x11).toNat = 0 := by
    rw [show (capOpenEmptyResult trapdoor positions).state =
      capOpenExitState (capOpenInitializedState
        (capProgram.initialState .opening (trapdoor, positions))) by rfl,
      cap_open_empty_report]
    rfl
  simp only [Submission.readProof, length, List.range_zero, List.map_nil, ite_self]

end CommitGolfCandidate
