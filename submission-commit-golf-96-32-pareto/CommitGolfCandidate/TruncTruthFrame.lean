import CommitGolfCandidate.TruncKeptRead
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 45000
attribute [local irreducible] checkEvaluation fixedParents parentProgram commitLeaves commitInputReady enterState readBuffer observedState

private theorem emptyParents (o : Oracle) (s : MachineState) : Consistent o (2^24-1) s := by
  intro i lo hi;change i<16777216 at hi;omega
private theorem enterGaps (s : MachineState) (g : Gaps s) : Gaps (enterState s) := by
  intro j hj
  exact (read_buffer_memory_congr (enterState s) s (entryMem s) (heapBase+96*j+64) 32).trans (g j hj)
private theorem observer {o : Oracle} {c : OracleComp World MachineState} (P : MachineState→Prop)
    (h : P (checkEvaluation o c).1) : P (observedState o c) := by unfold observedState;exact h

private theorem leafGaps (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) : Gaps (leavesState o m a) := by
  have h : Gaps (observedState o (commitLeaves (commitInputReady m a) (LENGTH/32))) :=
    observer Gaps (fun j hj=>commit_leaves_gap o m a j hj)
  rw [show LENGTH/32=2^19 by decide] at h
  exact h

theorem parentsTruth (o : Oracle) (m : Message) (a : BitVec (128*LENGTH)) : Consistent o 0 (parentsState o m a) :=
  parentsConsistent o (2^24-1) (enterState (leavesState o m a)) (startFrame o m a) (by decide)
    (emptyParents o _) (enterGaps _ (leafGaps o m a))
end CommitGolfCandidate.Trunc
