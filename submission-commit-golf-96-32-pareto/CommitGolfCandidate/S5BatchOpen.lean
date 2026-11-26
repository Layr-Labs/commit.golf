import CommitGolfCandidate.S5CapEnter
import CommitGolfCandidate.S5BatchCharge
import CommitGolfCandidate.S5BatchStart
import CommitGolfCandidate.S5FlushEnd
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Late (Levels SaltTape)
open Writer (widths)
attribute [local irreducible] execute List.range S5.encode energy S5.record Writer.measureField

private theorem batch_fields (tree : Levels) (salt : SaltTape) (xs : List Index) :
    recordFields tree salt xs++capFields tree xs 0 171=S5.batchFields tree salt xs := by
  simp only [recordFields,capFields,S5.batchFields,List.range_eq_range']

theorem batch_open (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape)
    (agree : TrapdoorAgrees td tree salt) (batch : ps.card=BATCH) :
    ∃ e : Execution, Artifact.submission.run .opening (td,ps)=pure e ∧ e.exit=.success ∧
      Artifact.submission.openingSucceeded e=true ∧ e.oracleCalls=0 ∧ e.cycles=Writer.batchCost (indices ps) ∧
      (WireFits tree → Artifact.submission.readProof e=S5.opening tree salt ps) := by
  let xs:=indices ps
  let records:=recordFields tree salt xs
  let caps:=capFields tree xs 0 171
  let v:=S5.encode (S5.batchFields tree salt xs)
  have len : xs.length=128:=(Finset.length_sort ..).trans batch
  have size : xs.length≤LENGTH:=by rw [len];decide
  obtain ⟨s,body,reg,cur,env⟩:=batch_records td ps tree salt agree batch
  obtain ⟨u,start,regs,input,c⟩:=cap_enter s xs tree salt records reg env cur
  have limit : widths records+230*171≤555170:=by rw [show widths records=_ from record_width_sum tree salt xs,len]
  obtain ⟨t,cap,last,_,packed⟩:=cap_loop u 0 171 xs tree salt records size (by decide) limit regs input c
  have fields : records++caps=S5.batchFields tree salt xs:=batch_fields tree salt xs
  have complete : ProofCursor (WireFits tree) t 555170 v := by
    change FieldCursor tree t (records++caps) at packed
    rw [fields] at packed
    have width : widths (S5.batchFields tree salt xs)=555170:=S5.batch_width tree salt xs len
    change ProofCursor (WireFits tree) t _ v at packed
    rwa [width] at packed
  have state:=flush_start complete (show t.pc=pcAt 381 from last.pc) last.proof
  let n:=recordSteps tree salt 0 xs
  let k:=capPrice xs 0 171+energy (widths records) caps
  let steps:=118+n+4+k
  let cycles:=118+(n+12*128)+4+k
  have total : cycles+34=Writer.batchCost xs:=cost_exact tree salt xs len
  have enough:=Writer.batch_bound xs len
  let slack:=68719476736-(steps+34)
  have frame : 68719476736=(slack+34)+steps:=by dsimp [slack,steps,cycles] at *;omega
  obtain ⟨z,halt,reported,data⟩:=flush_end t (WireFits tree) v state slack
  have all : Runs (initial td ps) t steps cycles:=(body.trans start).trans cap
  let e : Execution:=⟨.success,z,cycles+34,0⟩
  have run : Artifact.submission.run .opening (td,ps)=pure e:=by
    rw [open_abi,frame,all,halt,pure_bind];rfl
  have ok : Artifact.submission.openingSucceeded e=true:=by
    change (true && decide ((z.getReg .x11).toNat≤17179869184))=true;rw [reported];decide
  refine ⟨e,run,rfl,ok,rfl,total,?_⟩
  intro good
  let bs:=(List.range 69396).map (byteOf v)
  have normal : S5.opening tree salt ps=bs:=by unfold S5.opening;rw [if_pos batch];rfl
  have blen : bs.length=69396:=by simp only [bs,List.length_map,List.length_range]
  have out : HasBytes z proofBase bs:=by
    intro j h;rw [blen] at h
    simpa only [bs,List.getElem_map,List.getElem_range] using data good j h
  exact (read_proof z (cycles+34) bs (blen.symm ▸ reported) (by rw [blen];decide) out).2.trans normal.symm
end CommitGolfCandidate.S5Machine.Open
