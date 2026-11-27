import CommitGolfCandidate.Stage3cCapEnter
import CommitGolfCandidate.Stage3cCapLoop
import CommitGolfCandidate.Stage3cBatchCharge
import CommitGolfCandidate.Stage3cBatchStart
import CommitGolfCandidate.Stage3cFlushEnd
import CommitGolfCandidate.Stage3cOpeningCost
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (Levels SaltTape)
open Writer (widths)
attribute [local irreducible] execute List.range Binary.encode energy Binary.recordFields Writer.measureField

theorem cap_width (tree : Levels) (xs : List Index) (p n : Nat) : widths (capFields tree xs p n)=230*n := by
  induction n generalizing p with
  | zero=>rfl
  | succ n ih=>
    have e : widths (capFields tree xs p (n+1))=230+widths (capFields tree xs (p+1) n) := by
      simp only [capFields,List.range'_succ,List.map_cons,widths,List.sum_cons,Binary.slot]
    rw [e,ih];omega

theorem batch_open (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape)
    (agree : TrapdoorAgrees td tree salt) (batch : ps.card=BATCH) :
    ∃ e : Execution, Artifact.submission.run .opening (td,ps)=pure e ∧ e.exit=.success ∧
      Artifact.submission.openingSucceeded e=true ∧ e.oracleCalls=0 ∧ e.cycles=Writer.batchCost (indices ps) ∧
      (WireFits tree → Artifact.submission.readProof e=Binary.opening tree salt ps) := by
  let xs:=indices ps
  let records:=recordFields tree salt xs
  let caps:=capFields tree xs 0 256
  let v:=Binary.encode (records++caps)
  have len : xs.length=128:=(Finset.length_sort ..).trans batch
  have size : xs.length≤LENGTH:=by rw [len];decide
  obtain ⟨s,body,reg,cur,env⟩:=batch_records td ps tree salt agree batch
  obtain ⟨u,start,regs,input,c⟩:=cap_enter s xs tree salt records reg env cur
  have rw_ : widths records=3780*128:=by rw [show widths records=_ from record_width_sum tree salt xs,len]
  have limit : widths records+230*256≤542720:=by rw [rw_]
  obtain ⟨t,cap,last,_,packed⟩:=cap_loop u 0 256 xs tree salt records size (by decide) limit regs input c
  have complete : ProofCursor (WireFits tree) t 542720 v := by
    have width : widths (records++caps)=542720:=by rw [sum_append,rw_,cap_width]
    change ProofCursor (WireFits tree) t (widths (records++caps)) v at packed
    rwa [width] at packed
  have pc354 : t.pc=pcAt 354:=last.pc
  let n:=recordSteps tree salt 0 xs
  let k:=capPrice xs 0 256+energy (widths records) caps
  let steps:=101+n+4+k
  let cycles:=101+(n+3*128)+4+k
  have total : cycles+7=Writer.batchCost xs:=cost_exact tree salt xs len
  have enough:=Writer.batch_bound xs len
  let slack:=68719476736-(steps+7)
  have frame : 68719476736=(slack+7)+steps:=by dsimp [slack,steps,cycles] at *;omega
  obtain ⟨z,halt,reported,data⟩:=flush_end t (WireFits tree) v complete pc354 last.proof slack
  have all : Runs (initial td ps) t steps cycles:=(body.trans start).trans cap
  let e : Execution:=⟨.success,z,cycles+7,0⟩
  have run : Artifact.submission.run .opening (td,ps)=pure e:=by
    rw [open_abi,frame,all,halt,pure_bind];rfl
  have ok : Artifact.submission.openingSucceeded e=true:=by
    change (true && decide ((z.getReg .x11).toNat≤17179869184))=true;rw [reported];decide
  refine ⟨e,run,rfl,ok,rfl,total,?_⟩
  intro good
  let bs:=(List.range 67840).map (byteOf v)
  have model : Binary.opening tree salt ps=bs:=by
    unfold Binary.opening;rw [if_pos batch]
    unfold Binary.packed
    rw [Binary.field_geometry.2]
    have fields : (ps.sort (·≤·)).flatMap (Binary.recordFields tree salt)++(List.range 256).map (Binary.slot tree (ps.sort (·≤·)))=records++caps := by
      simp only [records,caps,recordFields,capFields,xs,indices,List.range_eq_range']
    rw [fields];rfl
  have blen : bs.length=67840:=by simp only [bs,List.length_map,List.length_range]
  have out : HasBytes z proofBase bs:=by
    intro j h;rw [blen] at h
    simpa only [bs,List.getElem_map,List.getElem_range] using data good j h
  exact (read_proof z (cycles+7) bs (blen.symm ▸ reported) (by rw [blen];decide) out).2.trans model.symm
end CommitGolfCandidate.Chained.BinaryMachine.Open
