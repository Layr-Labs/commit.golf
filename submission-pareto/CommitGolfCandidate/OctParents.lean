import CommitGolfCandidate.OctPairRemainder
import CommitGolfCandidate.FusedTree

/-! Peel one parent, execute the retained pair and quartet once, then share each
remaining branch across eight parents.
The N=1 and N=2 paths remain outside this positive-group composition. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

structure OctParentFetched (image : Image) : Prop where
  peeled : ParentTripleFetched image 4388
  peeledBranch : PeeledBranchFetched image
  pair : ParentSequenceFetched image 4316 2
  entryBranch : QuadBranchFetched image true
  first : ParentSequenceFetched image 4600 4
  firstBranch : OctBranchFetched image true
  sequence : ParentSequenceFetched image 4656 8
  branch : OctBranchFetched image false
  exit : OctExitFetched image

/-- Seven peeled parents plus eight-parent groups, including one terminal JAL.
For N=8, groups=0 and the retained quartet exits without entering the new body. -/
theorem oct_parents (image : Image) (fetched : OctParentFetched image)
    (state : MachineState) (groups : Nat) (bounded : 8 * groups + 7 < 2 ^ 24)
    (pointers : ParentPointerInvariant state (8 * groups + 7))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups + 7)) (fuel : Nat) :
    execute image (25 * groups + 25 + fuel) (state.setPC 4388) true =
      (do let finished ← commitParents state (8 * groups + 7)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (81 * groups + 74) (8 * groups + 7)) := by
  have firstAccess := fused_parent_access state (8 * groups + 7) (by omega) pointers buffers
  rw [show 25 * groups + 25 + fuel = 3 + (1 + (25 * groups + 21 + fuel)) by omega,
    fused_parent_triple image 4388 fetched.peeled state constants
      firstAccess.1 firstAccess.2.1 firstAccess.2.2.1 firstAccess.2.2.2]
  simp only [commitParents, bind_assoc]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer
  change BitVec 256 at answer
  let next := commitParentNextState (commitParentState state answer)
  have nextPointers : ParentPointerInvariant next (8 * groups + 6) :=
    commit_parent_step_pointers state answer (8 * groups + 6) pointers
  have nextConstants := fused_parent_constants state answer constants
  have nextBuffers := fused_parent_buffers state answer (8 * groups + 6) buffers
  change (do let result ← execute image (1 + (25 * groups + 21 + fuel))
               (next.setPC 4400) true
             return result.charge 10 1) = _
  rw [fused_peel_branch image fetched.peeledBranch next (4 * groups + 3) (by omega)
    (by convert nextPointers using 1 <;> congr 1 <;> omega)]
  simp only [show 4 * groups + 3 ≠ 0 by omega, ite_false]
  rw [oct_pair_remainder image fetched.pair fetched.entryBranch fetched.first fetched.firstBranch fetched.sequence
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
theorem oct_parents_execute (fetched : OctParentFetched (submission.image .commit))
    (state : MachineState) (groups : Nat) (messageBase : Word)
    (bounded : 8 * groups + 7 < 2 ^ 24) (pc : state.pc = 4388)
    (pointers : ParentPointerInvariant state (8 * groups + 7))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (8 * groups + 7)) (fuel : Nat) :
    execute (submission.image .commit) (25 * groups + 25 + fuel)
      (cursorBaseFrame state messageBase) true =
      (do let finished ← commitParents state (8 * groups + 7)
          let result ← execute (submission.image .commit) fuel
            ((cursorBaseFrame finished messageBase).setPC 4412) true
          return result.charge (81 * groups + 74) (8 * groups + 7)) := by
  have framedPC : (cursorBaseFrame state messageBase).pc = 4388 := pc
  have run := oct_parents _ fetched (cursorBaseFrame state messageBase) groups
    bounded pointers constants buffers fuel
  rw [← framedPC, hoist_pc_self] at run
  rw [cursor_base_parents_bind state (8 * groups + 7) messageBase
    (fun finished => do
      let result ← execute (submission.image .commit) fuel (finished.setPC 4412) true
      return result.charge (81 * groups + 74) (8 * groups + 7))] at run
  exact run

end CommitGolfCandidate
