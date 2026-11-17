import CommitGolfCandidate.FusedParentExit

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

theorem fused_parents (image : Image)
    (peeledFetched : ParentTripleFetched image 4388)
    (firstFetched : ParentTripleFetched image 4316)
    (secondFetched : ParentTripleFetched image 4328)
    (peeledBranch : PeeledBranchFetched image)
    (pairBranch : PairedBranchFetched image) (exitFetched : ParentExitFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * pairs + 1 < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * pairs + 1))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (2 * pairs + 1)) (fuel : Nat) :
    execute image (7 * pairs + 5 + fuel) (state.setPC 4388) true =
      (do let finished ← commitParents state (2 * pairs + 1)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (21 * pairs + 12) (2 * pairs + 1)) := by
  have firstAccess := fused_parent_access state (2 * pairs + 1) (by omega) pointers buffers
  rw [show 7 * pairs + 5 + fuel = 3 + (1 + (7 * pairs + 1 + fuel)) by omega,
    fused_parent_triple image 4388 peeledFetched state constants
      firstAccess.1 firstAccess.2.1 firstAccess.2.2.1 firstAccess.2.2.2]
  simp only [commitParents, bind_assoc]
  apply congrArg (fun tail =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= tail)
  funext answer
  change BitVec 256 at answer
  let next := commitParentNextState (commitParentState state answer)
  have nextPointers : ParentPointerInvariant next (2 * pairs) :=
    commit_parent_step_pointers state answer (2 * pairs) pointers
  have nextConstants := fused_parent_constants state answer constants
  have nextBuffers := fused_parent_buffers state answer (2 * pairs) buffers
  change (do let result ← execute image (1 + (7 * pairs + 1 + fuel))
               (next.setPC 4400) true
             return result.charge 10 1) = _
  rw [fused_peel_branch image peeledBranch next pairs (by omega) nextPointers]
  rw [fused_parent_remainder image firstFetched secondFetched pairBranch exitFetched
    next pairs (by omega) nextPointers nextConstants nextBuffers]
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

end CommitGolfCandidate
