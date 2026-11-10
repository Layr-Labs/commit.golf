import CommitGolfCandidate.CapOpenTraversalEntry
import CommitGolfCandidate.CapOpenDfsRun

/-! Bounded DFS execution from the actual nonempty opening loader. The record
and mark passes supply every traversal premise; no extra root/mark/cursor
admission hypothesis is added. Byte correctness and the return are separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_loaded_dfs_execute
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening)
        (capDfsInstructionTotal false (capOpenRequestedMarks positions) 510 (.visit 1)+fuel)
        (capOpenTraversalInitial trapdoor positions) allowCoins =
      (do let final ← capDfsRun false (capOpenRequestedMarks positions) 510 (.visit 1)
            (capOpenTraversalInitial trapdoor positions)
          let result ← execute (capProgram.image .opening) fuel final allowCoins
          return result.charge
            (capDfsCycleTotal false (capOpenRequestedMarks positions) 510 (.visit 1))
            (capDfsQueryTotal false (capOpenRequestedMarks positions) 510 (.visit 1))) := by
  simpa only [capWalkImage, Bool.false_eq_true, ite_false, capProgram, LOG_LENGTH] using
    cap_open_dfs_run_execute positions (capOpenRequestedMarks positions)
      (capOpenTraversalInitial trapdoor positions)
      (cap_open_traversal_initial_control trapdoor positions positive)
      (cap_open_traversal_initial_stable trapdoor positions positive)
      (cap_open_traversal_initial_marks trapdoor positions positive)
      (cap_open_traversal_initial_cursor trapdoor positions positive) fuel allowCoins

theorem cap_open_loaded_dfs_done
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (final : MachineState)
    (reached : final ∈ support (capDfsRun false (capOpenRequestedMarks positions)
      510 (.visit 1) (capOpenTraversalInitial trapdoor positions))) :
    final.pc = capAdvanceDone false ∧
      CapDfsStable false final capProgram.layout.trapdoor ∧
      CapMarksReady final 128 0 (capOpenRequestedMarks positions) ∧
      CapOpenCursorWindow capOpenOutputLimit .done final :=
  cap_open_dfs_run_done positions _ _ final
    (cap_open_traversal_initial_control trapdoor positions positive)
    (cap_open_traversal_initial_stable trapdoor positions positive)
    (cap_open_traversal_initial_marks trapdoor positions positive)
    (cap_open_traversal_initial_cursor trapdoor positions positive) reached

end CommitGolfCandidate
