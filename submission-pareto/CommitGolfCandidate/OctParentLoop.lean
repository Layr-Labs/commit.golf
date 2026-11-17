import CommitGolfCandidate.OctParentStep
import CommitGolfCandidate.QuadParentLoop

/-! Eight parents share one real end-pointer branch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

/-- Each fetched group has twenty-five instructions, eighty-one cycles and eight
queries. No terminal JAL is included in this loop theorem. -/
theorem oct_parents_loop (image : Image)
    (sequenceFetched : ParentSequenceFetched image 4656 8)
    (branchFetched : OctBranchFetched image false)
    (state : MachineState) (groups : Nat) (bounded : 8 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups)) (fuel : Nat) :
    execute image (25 * groups + fuel)
      (state.setPC (if groups = 0 then 4756 else 4656)) true =
      (do let finished ← commitParents state (8 * groups)
          let result ← execute image fuel (finished.setPC 4756) true
          return result.charge (81 * groups) (8 * groups)) := by
  induction groups generalizing state with
  | zero => simp [commitParents, Execution.charge]
  | succ groups ih =>
    have currentPointers : ParentPointerInvariant state (8 * groups + 8) := by
      convert pointers using 1 <;> congr 1 <;> omega
    have currentBuffers : ParentBuffers (state.getReg .x9) (8 * groups + 8) := by
      convert buffers using 1 <;> congr 1 <;> omega
    simp only [show groups + 1 ≠ 0 by omega, ite_false]
    rw [show 25 * (groups + 1) + fuel = 25 + (25 * groups + fuel) by omega,
      oct_sequence_branch image 4656 8 false sequenceFetched branchFetched rfl
        state groups (by omega) currentPointers constants currentBuffers]
    rw [show 8 * (groups + 1) = 8 + 8 * groups by omega, parent_sequence_comp]
    simp only [bind_assoc, octBranchPC, Bool.false_eq_true, ite_false]
    apply bind_congr_of_forall_mem_support
    intro middle reachable
    have invariants := parent_sequence_invariant state 8 (8 * groups)
      currentPointers constants currentBuffers middle reachable
    change (do
      let result ← execute image (25 * groups + fuel)
        (middle.setPC (if groups = 0 then 4756 else 4656)) true
      pure (result.charge (10 * 8 + 1) 8)) = _
    rw [ih middle (by omega) invariants.1 invariants.2.1 invariants.2.2]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (finished.setPC 4756) true >>= continuation)
    funext result
    congr 1
    cases result
    simp only [Execution.charge]
    congr 1 <;> omega

end CommitGolfCandidate
