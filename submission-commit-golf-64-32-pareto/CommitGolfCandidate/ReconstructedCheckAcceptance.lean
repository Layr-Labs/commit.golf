import CommitGolfCandidate.ReconstructedCheckCapTail
import CommitGolfCandidate.ReconstructedCheckCapRooted
import CommitGolfCandidate.ReconstructedCheckCapInitial
import CommitGolfCandidate.ReconstructedCheckRecordCap
import CommitGolfCandidate.ReconstructedCheckRecordClaims
import CommitGolfCandidate.ReconstructedCheckProofResult
import CommitGolfCandidate.ReconstructedCheckRecords
import CommitGolfCandidate.ReconstructedCheckReady

namespace CommitGolfCandidate.Reconstruction.CheckAcceptance
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckRecorded CheckLayout CheckRecordABI
open CheckRecordDecision CheckRecordLedger CheckRecordSlots CheckProofResult CheckLoader CheckCapLevel CheckCapIterate
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker
set_option maxRecDepth 12000
set_option maxHeartbeats 1450000
attribute [local irreducible] execute ArtifactEncoding.decode

private theorem atEnd {o : Oracle} {s : MachineState} {n : Nat} {w : Word} (last : CheckTailReturn.Finished o s n w) :
    End o s n (CheckHalt.exit w) := by
  intro f;have h:=last f;exact ⟨h.1,h.2.1,h.2.2.1⟩

private theorem finished (w : Word) : CheckHalt.exit w≠.unfinished:=by unfold CheckHalt.exit;split <;> decide

theorem cap (o : Oracle) (input : CheckInput) (s : MachineState) (a : Slots) (n : Nat) (rs : List PublicRow)
    (fits : input.proof.length≤Artifact.submission.sizes.proof) (pre : Segment o n (initial input) s rs)
    (prior : n≤835+4895*input.positions.card) (low : rs.length=84*input.positions.card)
    (start : Advance s input a input.positions.card) (history : Ledger o input input.positions.card a rs) : Report o input := by
  let c:=CheckRecordSpec.cursor input.positions.card
  let bits:=Wire.unpackBytes input.proof
  let len:=input.proof.length
  have maxCard:=positions_card_bound input.positions
  have space : c+630000≤70000000000:=by change 3633*input.positions.card+630000≤_;omega
  have maxLen : input.proof.length≤8355061248:=fits
  have bottom : CheckCapInitial.CanonicalBottom (CapEntry.flags input.positions) s:=by
    intro j hj live;obtain ⟨i,_,stored,canon⟩:=CheckRecordFrontier.cells history start.slots j hj live
    change Canonical 9 (CommitParents.cell s (4194304+32*(512+j)));rw [stored];exact canon
  obtain ⟨m,u,t,upper,out,cost,count,_,capRun,fr,mem,trail⟩:=CheckCapInitial.nine o input s c
    (by simpa only [ite_eq_left rfl,ite_true] using start.pc) start.fp start.sp start.cursor start.kept
    (CheckRecordFrontier.initial history start.slots) bottom space
  have allRun:=compose pre capRun
  have saved:=CheckHonestEndpoint.transfer fr start.kept
  have endAt:=CheckCapIterate.endState trail
  cases stop : out with
  | none=>
    rw [stop] at endAt
    have e : Rejected t:=endAt
    have end_:=CheckTailReturn.reject672 o t e.pc e.stack saved.ret
    apply publish o input fits t (n+m) 22 (rs++upper) (CheckHalt.exit (-1)) (by omega) allRun (atEnd end_) (finished _)
    rw [CheckTail.negative];intro h;cases h
  | some last=>
    rw [stop] at endAt
    have bdy : Boundary (CapEntry.flags input.positions) bits 0 last t:=endAt
    have b:=CheckCapTail.cursorBound trail last stop
    have fin : last≤70000000000:=by omega
    obtain ⟨h,hb,halt⟩:=CheckTail.run o t last len bits fin (by change input.proof.length<2^64;omega) (CheckCapTail.entry bdy fr start.kept)
    let status:=if CheckTail.Accepts t last len bits then BitVec.ofNat 64 len else (-1)
    apply publish o input fits t (n+m) h (rs++upper) (CheckHalt.exit status) (by omega) allRun (atEnd halt) (finished _)
    intro accepted
    have valid : CheckTail.Accepts t last len bits:=by
      by_contra no
      change CheckHalt.exit (if CheckTail.Accepts t last len bits then _ else (-1))=.success at accepted
      rw [ite_eq_right no,CheckTail.negative] at accepted;cases accepted
    have compare:=CheckCapTail.root saved valid.2.1
    rw [stop] at trail
    exact ⟨CheckRecordClaims.calls input rs upper low count,
      CheckRecordClaims.witness o input a rs (rs++upper) s history start.slots (fun _ h=>List.mem_append_left _ h)
        (CheckCapRooted.rooted input mem trail compare (fun _ h=>List.mem_append_right _ h))⟩

theorem run (o : Oracle) (input : CheckInput) : Report o input := by
  by_cases fits : input.proof.length≤Artifact.submission.sizes.proof
  · by_cases none : input.positions.card=0
    · exact emptyInput o input fits none
    · have pos : 0 < input.positions.card:=by omega
      have pre:=CheckReady.start o input pos fits
      by_cases ok : input.proof.length%8=0 ∧ CheckLaunchGate.minimum input.positions.card ≤ input.proof.length
      · rw [ite_eq_left ok] at pre
        obtain ⟨s,launch,start,count⟩:=pre
        obtain ⟨t,n,rs,cost,low,_,result⟩:=CheckRecords.positive o input s start pos count
        have scan : Segment o (835+n) (initial input) t rs:=by simpa only [List.nil_append] using compose launch low
        rcases result with ⟨wrong,_⟩|⟨⟨a,done,ledger⟩,number⟩
        · have bound:=positions_card_bound input.positions
          exact CheckProofResult.reject o input fits t (835+n) 20 rs (by omega) scan (CheckRecordClaims.reject o t wrong)
        · exact cap o input t a (835+n) rs fits scan (by omega) number done ledger
      · rw [ite_eq_right ok] at pre
        obtain ⟨n,limit,bad⟩:=pre
        exact CheckProofResult.reject o input fits (initial input) 0 n [] (by omega) (CheckRecorded.empty _ _) bad
  · exact tooLarge o input fits

theorem total : CheckCertificateFields.TotalChecker:=fun o input=>(run o input).1

theorem paths : Binding.AcceptedPaths Artifact.submission:=fun o input=>(run o input).2

end CommitGolfCandidate.Reconstruction.CheckAcceptance
