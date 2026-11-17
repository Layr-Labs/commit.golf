import CommitGolfCandidate.OctParentExit

/-! The retained pair leads to one four-parent block and then eight-parent groups. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

theorem oct_pair_remainder (image : Image)
    (pairFetched : ParentSequenceFetched image 4316 2)
    (entryBranch : QuadBranchFetched image true)
    (firstFetched : ParentSequenceFetched image 4600 4)
    (firstBranch : OctBranchFetched image true)
    (sequenceFetched : ParentSequenceFetched image 4656 8)
    (branchFetched : OctBranchFetched image false) (exitFetched : OctExitFetched image)
    (state : MachineState) (groups : Nat) (bounded : 8*groups+6<2^24)
    (pointers : ParentPointerInvariant state (8*groups+6))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (8*groups+6)) (fuel : Nat) :
    execute image (25*groups+21+fuel) (state.setPC 4316) true=
      (do let finished ← commitParents state (8*groups+6)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (81*groups+63) (8*groups+6)) := by
  have residual : 4*(2*groups+1)+2=8*groups+6 := by omega
  have pairedPointers : ParentPointerInvariant state (4*(2*groups+1)+2) := by
    rw [residual]
    exact pointers
  have pairedBuffers : ParentBuffers (state.getReg .x9) (4*(2*groups+1)+2) := by
    rw [residual]
    exact buffers
  rw [show 25*groups+21+fuel=7+(25*groups+14+fuel) by omega,
    parent_sequence_branch image 4316 2 true pairFetched entryBranch rfl state (2*groups+1)
      (by omega) pairedPointers constants pairedBuffers]
  rw [show 8*groups+6=2+(8*groups+4) by omega,parent_sequence_comp]
  simp only [bind_assoc,show 2*groups+1≠0 by omega,ite_false]
  apply bind_congr_of_forall_mem_support
  intro middle reachable
  have invariants := parent_sequence_invariant state 2 (8*groups+4)
    pointers constants buffers middle reachable
  change (do let result ← execute image (25*groups+14+fuel) (middle.setPC 4600) true
             return result.charge 21 2)=_
  rw [oct_quad_remainder image firstFetched firstBranch sequenceFetched branchFetched exitFetched
    middle groups (by omega) invariants.1 invariants.2.1 invariants.2.2]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished _
  apply congrArg (fun continuation => execute image fuel (finished.setPC 4412) true >>= continuation)
  funext result
  congr 1
  cases result
  simp only [Execution.charge]
  congr 1 <;> omega

end CommitGolfCandidate
