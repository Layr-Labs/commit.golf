import CommitGolfCandidate.R4bEntry
import CommitGolfCandidate.R4bLatch
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Open (BatchCursor initial)
open Machine (W Runs indexBase proofBase)
open Late (pcAt)

theorem allRows (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) :
    ∃ v,BatchCursor td ps v 128 ∧ Runs .opening (initial td ps) v 46573 48877 := by
  obtain ⟨s,start,atStart,frame⟩:=enter td ps batch
  have loop (t : Nat) (bound : t≤32) :
      ∃ v,Runs .opening s v (t*1454) (t*1526) ∧ v.pc=pcAt (nextSite t) ∧ Frame td ps t 0 v := by
    induction t with
    | zero=>exact ⟨s,Runs.refl .opening s,atStart,frame⟩
    | succ t ih=>
      obtain ⟨u,pre,site,current⟩:=ih (by omega)
      rw [nextSite,if_neg (by omega)] at site
      obtain ⟨a,body,after⟩:=tileRun td ps batch t (by omega) u current
      obtain ⟨run,ip⟩:=body.exec 16401 site (by rw [tileShape.1];decide) tileShape.2.2
      rw [tileShape.1,tileShape.2.1] at run
      rw [tileShape.1] at ip
      obtain ⟨z,branch,edge,done⟩:=latch td ps t (by omega) a ip after
      refine ⟨z,?_,edge,done⟩
      have e:=(pre.trans run).trans branch
      simpa only [Nat.succ_mul,Nat.add_assoc] using e
  obtain ⟨v,rows,exit,f⟩:=loop 32 le_rfl
  refine ⟨v,⟨⟨f.out,f.flagBase,f.one,f.consts .x27 3 rfl,f.buffer,f.sources,tapeDone batch f.cursor,f.flags⟩,
    exit,f.consts .x13 _ rfl,f.count⟩,start.trans rows⟩
end CommitGolfCandidate.R4b
