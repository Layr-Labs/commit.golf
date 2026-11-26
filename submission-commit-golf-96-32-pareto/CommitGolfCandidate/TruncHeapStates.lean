import CommitGolfCandidate.TruncParentData
import CommitGolfCandidate.TruncRuntime
import CommitGolfCandidate.CommitSemantics
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 350000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady

def CommittedState (o : Oracle) (m : Message) (s : MachineState) : Prop :=
  readBuffer s 4294971392 32=heapDigest s heapBase 1 ∧ Consistent o 0 s ∧
  ∀ i : Index,heapDigest s heapBase (LENGTH+i.val) =
    leafDigest o.compression i (readBuffer s (5905584160+16*i.val) 16) (m i)

noncomputable def observedState (o : Oracle) (c : OracleComp World MachineState) : MachineState := (checkEvaluation o c).1

noncomputable def leavesState (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) : MachineState :=
  observedState o (commitLeaves (commitInputReady m a) (2^19))
noncomputable def parentsState (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) : MachineState :=
  fixedParents o (2^24-1) (enterState (leavesState o m a))
noncomputable def returned (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) : MachineState :=
  commitExitState (commitRootCopyState (parentsState o m a))

end CommitGolfCandidate.Trunc
