import CommitGolfCandidate.TruncCommitTruth
import CommitGolfCandidate.TruncHidingTree
import CommitGolfCandidate.HidingSalts
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 240000
attribute [local irreducible] checkEvaluation parentProgram fixedParents commitLeaves

private theorem detBind (o : Oracle) {α β : Type} (c : OracleComp World α) (k : α→OracleComp World β)
    (first : o.run c=pure (checkEvaluation o c)) (last : ∀ x,o.run (k x)=pure (checkEvaluation o (k x))) :
    o.run (c>>=k)=pure (checkEvaluation o (c>>=k)) := by
  rw [oracle_run_bind,first,check_evaluation_bind];simp only [pure_bind,last]

private noncomputable def bodyFrom (c : OracleComp World MachineState) (q : Nat) : OracleComp World MachineState := do
  let l←c
  let t←parentProgram q (enterState l)
  return commitExitState (commitRootCopyState t)

private theorem fromDet (o : Oracle) (c : OracleComp World MachineState) (q : Nat)
    (det : o.run c=pure (checkEvaluation o c)) : o.run (bodyFrom c q)=pure (checkEvaluation o (bodyFrom c q)) := by
  unfold bodyFrom
  apply detBind o c _ det;intro l
  apply detBind o _ _ (by rw [parent_fixed_run,parent_eval]);intro t
  rw [oracle_run_pure,check_evaluation_pure]

theorem bodyDet (o : Oracle) (s : MachineState) : o.run (commitBody s)=pure (checkEvaluation o (commitBody s)) :=
  fromDet o (commitLeaves s (2^19)) (2^24-1) (commit_leaves_deterministic o s (2^19))

private theorem fromState (o : Oracle) (c : OracleComp World MachineState) (q : Nat) :
    (checkEvaluation o (bodyFrom c q)).1=commitExitState (commitRootCopyState (fixedParents o q (enterState (observedState o c)))) := by
  unfold bodyFrom observedState
  rw [check_evaluation_bind]
  rcases h : checkEvaluation o c with ⟨l,count⟩
  simp only [check_evaluation_bind,parent_eval,check_evaluation_pure]

theorem bodyExact (o : Oracle) (m : Message) {bits : Nat} (a : BitVec bits) :
    (checkEvaluation o (commitBody (commitInputReady m a))).1=returned o m a :=
  fromState o (commitLeaves (commitInputReady m a) (2^19)) (2^24-1)
end CommitGolfCandidate.Trunc
