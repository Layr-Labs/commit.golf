import CommitGolfCandidate.ReconstructedCheckRecordExit
import CommitGolfCandidate.ReconstructedCheckRecordLedger

namespace CommitGolfCandidate.Reconstruction.CheckRecords
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding CheckRecorded CheckLayout CheckRecordABI
open CheckRecordDecision CheckRecordLedger CheckRecordSlots
open TwoPermutationPrototype TwoPermutationPrototype.Sampling
set_option maxRecDepth 15000
set_option maxHeartbeats 1600000

def Accepted (o : Oracle) (input : CheckInput) (t : MachineState) (rs : List PublicRow) :=
  ∃ a : Slots,Advance t input a input.positions.card ∧ Ledger o input input.positions.card a rs

theorem loop (o : Oracle) (input : CheckInput) (remaining ord : Nat) (total : remaining+ord=input.positions.card)
    (s : MachineState) (a : Slots) (prior : List PublicRow) (atS : Advance s input a ord) (ledger : Ledger o input ord a prior) :
    ∃ t n rs,n≤4895*remaining ∧ Segment o n s t rs ∧ rs.length≤84*remaining ∧
      ((Failure t ∧ ¬GoodData o input) ∨ (Accepted o input t (prior++rs) ∧ rs.length=84*remaining)) := by
  induction remaining generalizing ord s a prior with
  | zero=>
    have last : ord=input.positions.card:=by omega
    subst ord;exact ⟨s,0,[],by decide,CheckRecorded.empty _ _,by decide,Or.inr ⟨⟨a,atS,by simpa using ledger⟩,rfl⟩⟩
  | succ remaining ih=>
    let i : Ordinal input:=⟨ord,by omega⟩
    have reg:=CheckRecordDecision.registers atS i.isLt
    obtain ⟨u,n,lim,path,pathEnd,canonical,lifts,card,ordinal,frame⟩:=CheckRecordFlight.positive o s input i atS.kept reg
    let parsed:=view o input i
    have pu:=CheckRecordFrame.persistent frame atS.kept
    have hu:=sameFrame atS.slots frame
    have read : Segment o n s u (log o input i):=path
    have size : (log o input i).length=84:=card
    obtain ⟨z,m,limM,exit,post⟩:=CheckRecordExit.positive o u input i a (index input i) parsed pu hu pathEnd
      (CheckRecordSpec.next o (index input i) (bits input) i (entryWords (message input i))) ordinal
    have sampled : Segment o (n+m) s z (log o input i):=by simpa only [List.append_nil] using compose read exit
    by_cases ok : CheckRecordExit.Accepts parsed a (index input i)
    · rw [ite_eq_left ok] at post
      have neu:=CheckRecordLedger.extend i ledger ok.2 canonical.2.2 (CheckRecordEvidence.lift o (index input i) (message input i) (bits input) (CheckRecordSpec.cursor i) lifts)
      obtain ⟨t,p,rest,small,replay,count,result⟩:=ih (i.val+1) (by dsimp [i];omega) z _ (prior++log o input i) post neu
      refine ⟨t,n+m+p,log o input i++rest,by omega,compose sampled replay,by rw [List.length_append,size];omega,?_⟩
      rcases result with bad|⟨good,number⟩
      · exact Or.inl bad
      · exact Or.inr ⟨by simpa only [List.append_assoc] using good,by rw [List.length_append,size,number];omega⟩
    · rw [ite_eq_right ok] at post
      exact ⟨z,n+m,log o input i,by omega,sampled,by omega,Or.inl ⟨post,fun valid=>ok ⟨(valid i).1,compatible ledger i valid⟩⟩⟩

theorem positive (o : Oracle) (input : CheckInput) (s : MachineState) (start : Start s input) (pos : 0 < input.positions.card)
    (count : s.getReg .x5=BitVec.ofNat 64 input.positions.card) :
    ∃ t n rs,n≤4895*input.positions.card ∧ Segment o n s t rs ∧ rs.length≤84*input.positions.card ∧
      ((Failure t ∧ ¬GoodData o input) ∨ (Accepted o input t rs ∧ rs.length=84*input.positions.card)) := by
  let a : Slots:=fun _=>none
  have begin : Advance s input a 0:=
    ⟨by simpa only [ite_eq_right (by omega : (0:Nat)≠input.positions.card)] using start.registers.pc,
    start.registers.sp,start.registers.fp,start.registers.ordinal,start.registers.cursor,start.registers.proof,start.registers.beginCopy,
    start.registers.endCopy,start.kept,CheckRecordSlots.empty s start.flags,count⟩
  simpa only [List.nil_append] using loop o input input.positions.card 0 (Nat.add_zero _) s a [] begin (CheckRecordLedger.empty o input)

end CommitGolfCandidate.Reconstruction.CheckRecords
