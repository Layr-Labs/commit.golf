import CommitGolfCandidate.ParentGroupLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem parent_group_prefix (image : Image) (start branchPC target : Word)
    (offset : BitVec 13) (count : Nat)
    (sequenceFetched : ParentSequenceFetched image start count)
    (branchFetched : ParentGroupBranchFetched image branchPC offset)
    (endPC : parentSequenceEnd start count=branchPC)
    (jump : branchPC+signExtend13 offset=target)
    (state : MachineState) (remaining : Nat) (positive : 0<remaining) (bounded : remaining<2^24)
    (pointers : ParentPointerInvariant state (remaining+count))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining+count)) (fuel : Nat) :
    execute image (3*count+1+fuel) (state.setPC start) true=
      (do let finished ← commitParents state count
          let result ← execute image fuel (finished.setPC target) true
          return result.charge (10*count+1) count) := by
  simpa only [if_neg (Nat.ne_of_gt positive)] using
    parent_group_sequence image start branchPC target offset count sequenceFetched branchFetched endPC jump
      state remaining bounded pointers constants buffers fuel

end CommitGolfCandidate
