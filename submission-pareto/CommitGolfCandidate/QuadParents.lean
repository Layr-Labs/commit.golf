import CommitGolfCandidate.QuadParentExit
import CommitGolfCandidate.FusedTree

/-! Peel one parent, execute the retained pair once, then share each remaining
branch across four parents. The challenge count is four times a positive Nat.
The N=1 and N=2 paths remain outside this positive-group composition. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

structure QuadParentFetched (image : Image) : Prop where
  peeled : ParentTripleFetched image 4388
  peeledBranch : PeeledBranchFetched image
  pair : ParentSequenceFetched image 4316 2
  entryBranch : QuadBranchFetched image true
  sequence : ParentSequenceFetched image 4600 4
  branch : QuadBranchFetched image false
  exit : QuadExitFetched image

/-- Three peeled parents plus four-parent groups, including one terminal JAL.
For N=4, groups=0 and the retained pair exits without entering the new body. -/
theorem quad_parents (image : Image) (fetched : QuadParentFetched image)
    (state : MachineState) (groups : Nat) (bounded : 4 * groups + 3 < 2 ^ 24)
    (pointers : ParentPointerInvariant state (4 * groups + 3))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups + 3)) (fuel : Nat) :
    execute image (13 * groups + 12 + fuel) (state.setPC 4388) true =
      (do let finished ← commitParents state (4 * groups + 3)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (41 * groups + 33) (4 * groups + 3)) := by
  have firstAccess := fused_parent_access state (4 * groups + 3) (by omega) pointers buffers
  rw [show 13 * groups + 12 + fuel = 3 + (1 + (13 * groups + 8 + fuel)) by omega,
    fused_parent_triple image 4388 fetched.peeled state constants
      firstAccess.1 firstAccess.2.1 firstAccess.2.2.1 firstAccess.2.2.2]
  simp only [commitParents, bind_assoc]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer
  change BitVec 256 at answer
  let next := commitParentNextState (commitParentState state answer)
  have nextPointers : ParentPointerInvariant next (4 * groups + 2) :=
    commit_parent_step_pointers state answer (4 * groups + 2) pointers
  have nextConstants := fused_parent_constants state answer constants
  have nextBuffers := fused_parent_buffers state answer (4 * groups + 2) buffers
  change (do let result ← execute image (1 + (13 * groups + 8 + fuel))
               (next.setPC 4400) true
             return result.charge 10 1) = _
  rw [fused_peel_branch image fetched.peeledBranch next (2 * groups + 1) (by omega)
    (by convert nextPointers using 1 <;> congr 1 <;> omega)]
  simp only [show 2 * groups + 1 ≠ 0 by omega, ite_false]
  rw [quad_pair_remainder image fetched.pair fetched.entryBranch fetched.sequence
    fetched.branch fetched.exit next groups (by omega) nextPointers nextConstants nextBuffers]
  dsimp only [next]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  apply congrArg (fun continuation =>
    execute image fuel (finished.setPC 4412) true >>= continuation)
  funext result
  congr 1
  cases result
  simp only [Execution.charge]
  congr 1 <;> omega

/-- Transport the retained x8/x21 base-register frame through the new parents. -/
theorem quad_parents_execute (fetched : QuadParentFetched (submission.image .commit))
    (state : MachineState) (groups : Nat) (messageBase : Word)
    (bounded : 4 * groups + 3 < 2 ^ 24) (pc : state.pc = 4388)
    (pointers : ParentPointerInvariant state (4 * groups + 3))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (4 * groups + 3)) (fuel : Nat) :
    execute (submission.image .commit) (13 * groups + 12 + fuel)
      (cursorBaseFrame state messageBase) true =
      (do let finished ← commitParents state (4 * groups + 3)
          let result ← execute (submission.image .commit) fuel
            ((cursorBaseFrame finished messageBase).setPC 4412) true
          return result.charge (41 * groups + 33) (4 * groups + 3)) := by
  have framedPC : (cursorBaseFrame state messageBase).pc = 4388 := pc
  have run := quad_parents _ fetched (cursorBaseFrame state messageBase) groups
    bounded pointers constants buffers fuel
  rw [← framedPC, hoist_pc_self] at run
  rw [cursor_base_parents_bind state (4 * groups + 3) messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel (finished.setPC 4412) true
      return result.charge (41 * groups + 33) (4 * groups + 3))] at run
  exact run

end CommitGolfCandidate
