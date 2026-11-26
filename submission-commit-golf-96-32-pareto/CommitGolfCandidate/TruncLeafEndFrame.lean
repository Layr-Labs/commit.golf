import CommitGolfCandidate.TruncHeapStates
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState

set_option maxHeartbeats 25000
private theorem evalFrame (o : Oracle) (c : OracleComp World MachineState) (q : Nat)
    (all : ∀ z,z∈support c → ParentFrame q (enterState z)) :
    ParentFrame q (enterState (observedState o c)) :=
  all _ (check_evaluation_support o c)

attribute [local irreducible] observedState in
theorem startFrame (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) :
    ParentFrame (2^24-1) (enterState (leavesState o m a)) :=
  evalFrame o (commitLeaves (commitInputReady m a) (2^19)) (2^24-1) (readyFrame m a)
end CommitGolfCandidate.Trunc
