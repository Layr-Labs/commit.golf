import CommitGolfCandidate.ParentGroupBranch
import CommitGolfCandidate.QuadParentLoop

/-! A parameterized branch-sharing loop, with all image fetches and encoded jumps explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

/-- One pointer branch is shared by an arbitrary positive number of parent queries. -/
theorem parent_group_loop (image : Image) (start branchPC : Word) (offset : BitVec 13)
    (width : Nat) (positive : 0<width)
    (sequenceFetched : ParentSequenceFetched image start width)
    (branchFetched : ParentGroupBranchFetched image branchPC offset)
    (endPC : parentSequenceEnd start width=branchPC)
    (jump : branchPC+signExtend13 offset=start)
    (state : MachineState) (groups : Nat) (bounded : width*groups<2^24)
    (pointers : ParentPointerInvariant state (width*groups))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (width*groups)) (fuel : Nat) :
    execute image ((3*width+1)*groups+fuel)
      (state.setPC (if groups=0 then branchPC+4 else start)) true=
      (do let finished ← commitParents state (width*groups)
          let result ← execute image fuel (finished.setPC (branchPC+4)) true
          return result.charge ((10*width+1)*groups) (width*groups)) := by
  induction groups generalizing state with
  | zero => simp [commitParents,Execution.charge]
  | succ groups ih =>
    have residual : width*(groups+1)=width*groups+width := by simp [Nat.mul_succ]
    have currentPointers : ParentPointerInvariant state (width*groups+width) := by
      rw [← residual]
      exact pointers
    have currentBuffers : ParentBuffers (state.getReg .x9) (width*groups+width) := by
      rw [← residual]
      exact buffers
    have smaller : width*groups<2^24 := by rw [residual] at bounded;omega
    simp only [Nat.succ_ne_zero,ite_false]
    rw [show (3*width+1)*(groups+1)+fuel=3*width+1+((3*width+1)*groups+fuel) by
        simp [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm],
      parent_group_sequence image start branchPC start offset width sequenceFetched branchFetched endPC jump
        state (width*groups) smaller currentPointers constants currentBuffers]
    rw [show width*(groups+1)=width+width*groups by simp [Nat.mul_succ,Nat.add_comm],parent_sequence_comp]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    have invariants := parent_sequence_invariant state width (width*groups)
      currentPointers constants currentBuffers middle reached
    have empty : width*groups=0 ↔ groups=0 := by
      simp [Nat.mul_eq_zero,Nat.ne_of_gt positive]
    change (do let result ← execute image ((3*width+1)*groups+fuel)
                 (middle.setPC (if width*groups=0 then branchPC+4 else start)) true
               return result.charge (10*width+1) width)=_
    simp only [empty]
    rw [ih middle smaller invariants.1 invariants.2.1 invariants.2.2]
    simp only [bind_assoc,pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation => execute image fuel (finished.setPC (branchPC+4)) true >>= continuation)
    funext result
    congr 1
    cases result
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate
