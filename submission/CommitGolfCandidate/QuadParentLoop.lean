import CommitGolfCandidate.QuadParentStep

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

theorem parent_sequence_comp (state : MachineState) (first second : Nat) :
    commitParents state (first + second) =
      (do let middle ← commitParents state first
          commitParents middle second) := by
  induction first generalizing state with
  | zero => simp [commitParents]
  | succ first ih =>
    rw [show first + 1 + second = (first + second) + 1 by omega]
    simp only [commitParents, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (commitParentQuery state))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    exact ih (commitParentNextState (commitParentState state answer))

theorem quad_parents_loop (image : Image)
    (sequenceFetched : ParentSequenceFetched image 4600 4)
    (branchFetched : QuadBranchFetched image false)
    (state : MachineState) (groups : Nat) (bounded : 4 * groups < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups)) (fuel : Nat) :
    execute image (13 * groups + fuel)
      (state.setPC (if groups = 0 then 4652 else 4600)) true =
      (do let finished ← commitParents state (4 * groups)
          let result ← execute image fuel (finished.setPC 4652) true
          return result.charge (41 * groups) (4 * groups)) := by
  induction groups generalizing state with
  | zero => simp [commitParents, Execution.charge]
  | succ groups ih =>
    have currentPointers : ParentPointerInvariant state (4 * groups + 4) := by
      convert pointers using 1 <;> congr 1 <;> omega
    have currentBuffers : ParentBuffers (state.getReg .x9) (4 * groups + 4) := by
      convert buffers using 1 <;> congr 1 <;> omega
    simp only [show groups + 1 ≠ 0 by omega, ite_false]
    rw [show 13 * (groups + 1) + fuel = 13 + (13 * groups + fuel) by omega,
      parent_sequence_branch image 4600 4 false sequenceFetched branchFetched rfl
        state groups (by omega) currentPointers constants currentBuffers]
    rw [show 4 * (groups + 1) = 4 + 4 * groups by omega, parent_sequence_comp]
    simp only [bind_assoc, quadBranchPC, Bool.false_eq_true, ite_false]
    apply bind_congr_of_forall_mem_support
    intro middle reachable
    have invariants := parent_sequence_invariant state 4 (4 * groups)
      currentPointers constants currentBuffers middle reachable
    change (do
      let result ← execute image (13 * groups + fuel)
        (middle.setPC (if groups = 0 then 4652 else 4600)) true
      pure (result.charge (10 * 4 + 1) 4)) = _
    rw [ih middle (by omega) invariants.1 invariants.2.1 invariants.2.2]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (finished.setPC 4652) true >>= continuation)
    funext result
    congr 1
    cases result
    simp only [Execution.charge]
    congr 1 <;> omega

end CommitGolfCandidate
