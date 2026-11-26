import CommitGolfCandidate.TruncBatchEvaluation
import CommitGolfCandidate.TruncNormalEvaluation
import CommitGolfCandidate.Stage3HonestCap
import CommitGolfCandidate.LateResources2

namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 200000
attribute [local irreducible] Late.Check.Normal.checkEvaluation Batch.obs readBuffer

private theorem replaceValue (i : CheckInput) (p : Proof) (r : Nat) :
    recordValue {i with proof:=p} r=recordValue i r := rfl
private theorem replaceRecord (i : CheckInput) (p : Proof) (r : Nat) :
    recordIndex {i with proof:=p} r=recordIndex i r := rfl

attribute [local irreducible] unpack in
private theorem wideValue (i : CheckInput) (r : Nat) : recordValue (wideInput i) r=recordValue i r := by
  by_cases b : i.positions.card=BATCH
  · rw [wideInput,if_pos b];exact replaceValue i (unpack i.proof) r
  · rw [wideInput,if_neg b]

attribute [local irreducible] unpack in
private theorem wideRecord (i : CheckInput) (r : Nat) : recordIndex (wideInput i) r=recordIndex i r := by
  by_cases b : i.positions.card=BATCH
  · rw [wideInput,if_pos b];exact replaceRecord i (unpack i.proof) r
  · rw [wideInput,if_neg b]

private theorem wideCommit (i : CheckInput) : (wideInput i).commitment=i.commitment := by unfold wideInput;split <;> rfl

theorem checkedSound : CheckSound := by
  intro o i accepted r hr
  rw [Late.Check.Normal.scheme_check_evaluation] at accepted
  have success : (Late.Check.Normal.checkEvaluation o (submission.run .check i)).1.exit=.success := beq_iff_eq.mp accepted
  by_cases batch : i.positions.card=BATCH
  · have g:=((batchEvaluation o i batch).2.2.mp success).2
    have h:=batchImpliesRoot o (wideInput i) g r (by rw [batch] at hr;exact hr)
    simpa only [authSalt,authSibling,if_pos batch,wideRecord,wideValue,wideCommit] using h
  · have h:=((Normal.evaluate o i batch).2.2.mp success).2 r hr
    simpa only [authSalt,authSibling,if_neg batch,Normal.mathRoot] using h

theorem checkResources (o : Oracle) (i : CheckInput) :
    let out:=Late.Check.Normal.checkEvaluation o (submission.run .check i)
    out.1.exit≠.unfinished ∧ out.2≤CHECK_BUDGET i.positions.card := by
  by_cases b : i.positions.card=BATCH
  · have h:=batchEvaluation o i b
    exact ⟨h.1,h.2.1.trans (by rw [b];decide)⟩
  · have h:=Normal.evaluate o i b
    exact ⟨h.1,h.2.1.trans (by unfold CHECK_BUDGET;omega)⟩

end CommitGolfCandidate.Trunc
