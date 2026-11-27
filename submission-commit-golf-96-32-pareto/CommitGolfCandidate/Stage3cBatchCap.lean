import CommitGolfCandidate.Stage3cCapJudgment
import CommitGolfCandidate.Stage3cCapPairs
import CommitGolfCandidate.Stage3cUpperLoop
import CommitGolfCandidate.Stage3cRootJudge
import CommitGolfCandidate.Stage3cCheckSystem
import CommitGolfCandidate.Stage3cBatchJudge
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
theorem batch_of_cap (judge : CapJudgment) : BatchChecker := by
  intro o x s card size pc regs mem
  have law : Pw.wireValid o.compression x ↔ Consistent o.compression x 128 ∧ ∃ q,rootMatches o.compression x q:=by
    rw [Pw.wireValid,if_pos card]
    constructor
    · rintro ⟨_,h⟩
      have g:=(batch_condition _ _).mp h
      exact ⟨g.1,0,g.2⟩
    · rintro ⟨rows,q,root⟩;exact ⟨size,(batch_condition _ _).mpr ⟨rows,root⟩⟩
  rcases batch_rows o x 0 128 s card rfl pc regs (buckets_initial _ _ _ mem) (fun _ h=>by omega) with good|bad
  · obtain ⟨all,⟨u,k,lim,rows,ep,rr,table⟩⟩:=good
    obtain ⟨v,first,zero⟩:=slot_entry o x u ep rr table
    obtain ⟨w,b,bs,read,slots_⟩:=slots o x 0 256 v (by decide) zero
    obtain ⟨z,entry,start⟩:=pair_entry o x w slots_
    obtain ⟨a,n,q,ns,qs,pair,done_⟩:=pairs o x 0 256 z start (by decide)
    obtain ⟨t,m,ms,up_,tip,env,evidence,cache⟩:=build_upper o x a done_
    have end_:=judge o x t tip env evidence cache
    have flow:=((((rows.trans first).trans read).trans entry).trans pair).trans up_
    have pb:=pair_total_bound o.compression x
    exact (Outcome.prefix flow end_).weaken (Iff.trans ⟨fun h=>⟨all,h⟩,And.right⟩ law.symm) (by omega) (by omega)
  · obtain ⟨invalid,⟨k,q,lim,qs,rejected⟩⟩:=bad
    exact ⟨⟨k,q,.failure,by omega,by omega,by decide,reject_iff (fun ok=>invalid (law.mp ok).1),rejected⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
