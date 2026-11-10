import CommitGolfCandidate.CapOpenLoadedBytes
import CommitGolfCandidate.CapOpenPure

/-! The nonempty opening's deterministic execution result and actual
readProof bytes. Successful output capacity follows from the retained ABI;
honest heap semantics are not assumed by this image-level result. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenFinalState
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : MachineState :=
  capOpenDfsFinal (capOpenRequestedMarks positions) 510 (.visit 1)
    (capOpenTraversalInitial trapdoor positions)

def capOpenNonemptyResult
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : Execution :=
  ⟨.success, capOpenExitState (capOpenFinalState trapdoor positions),
    29+278*positions.card+1272+2+
      capDfsCycleTotal false (capOpenRequestedMarks positions) 510 (.visit 1)+4, 0⟩

theorem cap_open_final_state_support
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    capOpenFinalState trapdoor positions ∈ support
      (capDfsRun false (capOpenRequestedMarks positions) 510 (.visit 1)
        (capOpenTraversalInitial trapdoor positions)) := by
  rw [cap_open_dfs_run_pure]
  simp only [capOpenFinalState, support_pure, Set.mem_singleton_iff]

theorem cap_open_nonempty_result_length
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    ((capOpenNonemptyResult trapdoor positions).state.getReg .x11).toNat =
      (capOpenLoadedBytes trapdoor positions).length :=
  cap_open_loaded_bytes_report trapdoor positions positive _
    (cap_open_final_state_support trapdoor positions)

theorem cap_open_loaded_bytes_capacity
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (capOpenLoadedBytes trapdoor positions).length ≤ capProgram.sizes.proof := by
  have count := cap_control_boundaries_length (capOpenRequestedMarks positions) 510 (.visit 1)
  have space := (cap_open_abi_output_space positions).1
  rw [cap_open_loaded_bytes_length]
  simp only [capOpenBoundaryDigests, List.length_map]
  omega

theorem cap_open_nonempty_succeeded
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    capProgram.openingSucceeded (capOpenNonemptyResult trapdoor positions) = true := by
  simp only [Submission.openingSucceeded, cap_open_nonempty_result_length _ _ positive]
  change (true && decide ((capOpenLoadedBytes trapdoor positions).length ≤
    capProgram.sizes.proof)) = true
  simp only [Bool.true_and, decide_eq_true_eq]
  exact cap_open_loaded_bytes_capacity trapdoor positions

theorem cap_open_nonempty_read_proof
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) :
    capProgram.readProof (capOpenNonemptyResult trapdoor positions) =
      capOpenLoadedBytes trapdoor positions := by
  simp only [Submission.readProof, cap_open_nonempty_succeeded _ _ positive,
    ↓reduceIte, cap_open_nonempty_result_length _ _ positive]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro offset first second
    simp only [List.getElem_map, List.getElem_range]
    have bytes := cap_open_loaded_bytes_byte trapdoor positions positive _
      (cap_open_final_state_support trapdoor positions) offset second
    simpa only [capOpenNonemptyResult, List.getElem?_eq_getElem second,
      Option.getD_some] using bytes

end CommitGolfCandidate
