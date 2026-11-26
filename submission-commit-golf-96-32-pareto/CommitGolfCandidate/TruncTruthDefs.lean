import CommitGolfCandidate.TruncLeafEndFrame
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState

set_option maxHeartbeats 25000
theorem finalFrame (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) : ParentFrame 0 (parentsState o m a) := by
  unfold parentsState
  exact parent_final_frame o (2^24-1) (enterState (leavesState o m a)) (startFrame o m a)

end CommitGolfCandidate.Trunc
