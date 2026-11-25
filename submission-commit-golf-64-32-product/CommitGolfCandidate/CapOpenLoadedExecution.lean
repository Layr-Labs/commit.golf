import CommitGolfCandidate.CapOpenLoadedDfs
import CommitGolfCandidate.CapOpenExit
import CommitGolfCandidate.BoundaryPotential
import CommitGolfCandidate.CapBoundarySize

/-! Complete finite-fuel execution of every nonempty experimental opening,
including the real success HALT. It charges the actual record count and DFS
macro costs, with zero public or coin queries. This runtime theorem does not
yet identify the output bytes with the honest cap codec. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem exit_charges (state : MachineState) (entryCost traversal : Nat) :
    ((Execution.mk .success state 4 0).charge traversal 0).charge entryCost 0 =
      ⟨.success, state, entryCost+traversal+4, 0⟩ := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc]

private theorem open_query_total (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) :
    capDfsQueryTotal false marked count control = 0 := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
    rw [capDfsQueryTotal, cap_dfs_step_open_queries, ih, Nat.zero_add]

theorem cap_open_loaded_execution
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening)
        (29+263*positions.card+2552+2+
          capDfsInstructionTotal false (capOpenRequestedMarks positions) 1022 (.visit 1)+4+fuel)
        (capProgram.initialState .opening (trapdoor, positions)) allowCoins =
      (do let final ← capDfsRun false (capOpenRequestedMarks positions) 1022 (.visit 1)
            (capOpenTraversalInitial trapdoor positions)
          return ⟨.success, capOpenExitState final,
            29+266*positions.card+2552+2+
              capDfsCycleTotal false (capOpenRequestedMarks positions) 1022 (.visit 1)+4, 0⟩) := by
  rw [show 29+263*positions.card+2552+2+
        capDfsInstructionTotal false (capOpenRequestedMarks positions) 1022 (.visit 1)+4+fuel =
      29+263*positions.card+2552+2+
        (capDfsInstructionTotal false (capOpenRequestedMarks positions) 1022 (.visit 1)+(4+fuel))
      by omega, cap_open_traversal_entry_execute trapdoor positions positive,
    cap_open_loaded_dfs_execute trapdoor positions positive]
  simp only [bind_assoc, pure_bind, open_query_total]
  apply bind_congr_of_forall_mem_support
  intro final reached
  have pc := (cap_open_loaded_dfs_done trapdoor positions positive final reached).1
  have exit : execute (capProgram.image .opening) (4+fuel) final allowCoins =
      pure ⟨.success, capOpenExitState final, 4, 0⟩ := by
    simpa only [capWalkImage, Bool.false_eq_true, ite_false, capProgram, LOG_LENGTH] using
      cap_open_exit final pc fuel allowCoins
  rw [exit]
  simp only [pure_bind, exit_charges]

theorem cap_open_loaded_batch_cycles (positions : Positions) (batch : positions.card = 128) :
    29+266*positions.card+2552+2+
      capDfsCycleTotal false (capOpenRequestedMarks positions) 1022 (.visit 1)+4 ≤ 43531 := by
  have traversal := cap_boundary_cycle_bound (capOpenRequestedMarks positions)
  have positive : 0 < positions.card := by omega
  have boundary := cap_open_requested_boundary_bound positions positive
  rw [batch]
  omega

end CommitGolfCandidate
