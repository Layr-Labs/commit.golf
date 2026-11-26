import CommitGolfCandidate.TruncBatchEvaluation
import CommitGolfCandidate.TruncNormalEvaluation
import CommitGolfCandidate.TruncHonestWide
import CommitGolfCandidate.TruncHonestNormal
import CommitGolfCandidate.TruncHonestPacking
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 200000
attribute [local irreducible] checkEvaluation Batch.obs readBuffer Open.openingResult

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
  rw [scheme_check_evaluation] at accepted
  have success : (checkEvaluation o (submission.run .check i)).1.exit=.success := beq_iff_eq.mp accepted
  by_cases batch : i.positions.card=BATCH
  · have g:=((batchEvaluation o i batch).2.2.mp success).2
    have h:=batchImpliesRoot o (wideInput i) g r (by rw [batch] at hr;exact hr)
    simpa only [authSalt,authSibling,if_pos batch,wideRecord,wideValue,wideCommit] using h
  · have h:=((Normal.evaluate o i batch).2.2.mp success).2 r hr
    simpa only [authSalt,authSibling,if_neg batch,Normal.mathRoot] using h

theorem checkResources (o : Oracle) (i : CheckInput) :
    let out:=checkEvaluation o (submission.run .check i)
    out.1.exit≠.unfinished ∧ out.2≤CHECK_BUDGET i.positions.card := by
  by_cases b : i.positions.card=BATCH
  · have h:=batchEvaluation o i b
    exact ⟨h.1,h.2.1.trans (by rw [b];decide)⟩
  · have h:=Normal.evaluate o i b
    exact ⟨h.1,h.2.1.trans (by unfold CHECK_BUDGET;omega)⟩

def honestInput (s : MachineState) (m : Message) (ps : Positions) : CheckInput :=
  ⟨readBuffer s submission.layout.commitment 32,ps,m.restrict ps,
    submission.readProof (Open.openingResult (readBuffer s submission.layout.trapdoor submission.sizes.trapdoor) ps)⟩

theorem wideHonest (bytes : Wire.PackedBytes) (o : Oracle) (m : Message) (s : MachineState)
    (ok : CommittedState o m s) (ps : Positions) (b : ps.card=BATCH) :
    wideInput (honestInput s m ps)=PairCap.honestInput s m ps := by
  unfold wideInput
  rw [if_pos (show (honestInput s m ps).positions.card=BATCH from b)]
  let td:=PairCap.saved s
  have eqn : (honestInput s m ps).proof=pack (PairCap.honestInput s m ps).proof :=
    packedProof bytes td ps b
  change {PairCap.honestInput s m ps with proof:=unpack (honestInput s m ps).proof}=_
  rw [eqn,honestRoundTrip o m s ok ps b]

theorem normalHonest (bytes : Wire.PackedBytes) (m : Message) (s : MachineState) (ps : Positions) (b : ps.card≠BATCH) :
    honestInput s m ps=normalInput s m ps := by
  unfold honestInput normalInput
  rw [outputConversion bytes s ps,publicProof,if_neg b];rfl

theorem acceptsHonest (bytes : Wire.PackedBytes) (o : Oracle) (m : Message) (s : MachineState)
    (correct : CommittedState o m s) (ps : Positions) :
    let i:=honestInput s m ps
    (o.eval (submission.scheme.check i.commitment i.positions i.values i.proof)).1=true := by
  let i:=honestInput s m ps
  apply (congrArg Prod.fst (scheme_check_evaluation o submission i)).trans
  apply beq_iff_eq.mpr
  have length:=Open.opening_proof_length (PairCap.saved s) ps
  by_cases b : ps.card=BATCH
  · apply (batchEvaluation o i b).2.2.mpr
    refine ⟨length.trans (by simp [Open.proofBytes,b] <;> rfl),?_⟩
    rw [wideHonest bytes o m s correct ps b];exact honestModel o m s correct ps b
  · apply (Normal.evaluate o i b).2.2.mpr
    refine ⟨length.trans (by simp [Open.proofBytes,b] <;> rfl),?_⟩
    intro r hr;change Normal.mathRoot o (honestInput s m ps) r=(honestInput s m ps).commitment
    rw [normalHonest bytes m s ps b]
    exact honestNormal o m s correct ps b r hr

end CommitGolfCandidate.Trunc
