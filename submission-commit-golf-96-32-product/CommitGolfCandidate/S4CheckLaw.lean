import CommitGolfCandidate.S4BatchRoot
import CommitGolfCandidate.S4Resources
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 5000

private theorem withinCapacity (H : Compression) (i : CheckInput) (accepts : wireValid H i) :
    i.proof.length≤Late.submission.sizes.proof:=by
  have count:=boundedCount i
  change i.proof.length≤17179869184
  unfold wireValid at accepts
  split at accepts
  · exact accepts.1 ▸ (by decide : 70410≤17179869184)
  · obtain ⟨width,_⟩:=accepts;omega

private theorem admittedRun (c : Submission) (i : CheckInput) (fits : i.proof.length≤c.sizes.proof) :
    c.run .check i=execute (c.image .check) (c.steps .check) (c.initialState .check i) false:=by
  simp only [Submission.run,fits,decide_true,ite_true];rfl
private theorem refusedRun (c : Submission) (i : CheckInput) (tooLarge : ¬i.proof.length≤c.sizes.proof) :
    c.run .check i=pure ⟨.failure,initialMachine,0,0⟩:=by simp only [Submission.run,decide_eq_false tooLarge,Bool.false_eq_true,ite_false]

attribute [local irreducible] execute wireValid checkEvaluation
theorem checkResult (o : Oracle) (i : CheckInput) :
    let e:=checkEvaluation o (Late.submission.run .check i)
    e.1.exit≠.unfinished ∧ e.2≤CHECK_BUDGET i.positions.card ∧ (e.1.exit=.success ↔ wireValid o.compression i) := by
  by_cases fits : i.proof.length≤Late.submission.sizes.proof
  · have eval : Evaluation o i:=by
      by_cases b:i.positions.card=BATCH
      · exact batchEvaluation o i b fits
      · exact ordinaryEvaluation o i b fits
    obtain ⟨n,q,le,limit,⟨ex,closed,iff,fin⟩⟩:=eval
    have eqv:=fin (1099511627776-n)
    rw [show n+(1099511627776-n)=1099511627776 by omega] at eqv
    let e:=checkEvaluation o (Late.submission.run .check i)
    have raw : Late.submission.run .check i=execute Code.check.image 1099511627776 (initial i) false:=
      (admittedRun Late.submission i fits).trans (congrArg (fun n=>execute (Late.submission.image .check) n (Late.submission.initialState .check i) false)
        (show Late.submission.steps .check=1099511627776 from rfl))
    have result : (e.1.exit,e.2)=(ex,q):=by dsimp only [e];rw [raw];exact eqv
    have outcome : e.1.exit=ex:=congrArg Prod.fst result
    have calls : e.2=q:=congrArg Prod.snd result
    change e.1.exit≠.unfinished ∧ e.2≤_ ∧ (e.1.exit=.success ↔ _)
    rw [outcome,calls];exact ⟨closed,limit,iff⟩
  · rw [refusedRun Late.submission i fits,check_evaluation_pure]
    exact ⟨by decide,Nat.zero_le _,⟨(fun e=>by cases e),fun valid=>False.elim (fits (withinCapacity _ _ valid))⟩⟩

theorem machineChecker : CheckLaw where
  terminates o i:=(checkResult o i).1
  valid o i:=by rw [accepted,scheme_check_evaluation];exact beq_iff_eq.trans (checkResult o i).2.2
  calls o i:=by rw [scheme_check_evaluation];exact (checkResult o i).2.1

end CommitGolfCandidate.S4.Machine
