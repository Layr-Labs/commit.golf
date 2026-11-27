import CommitGolfCandidate.Stage3cRootJudge
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
def CapJudgment := ∀ (o : Oracle) (x : CheckInput) (s : MachineState),s.pc=pcAt 1084 →
    CapEnv x s → Evidence o.compression x 0 s → Cache s (capVal o.compression x 0) →
    Outcome o s (∃ q,rootMatches o.compression x q) 5000 72

/-- ptr transmits every cap bit, so the judgment is the single root comparison. -/
theorem cap_judgment : CapJudgment := by
  intro o x s pc env ev cache
  obtain ⟨u,k,lim,cmp,ip,mem,keep⟩:=root_judge o x s false 0 pc env cache
  by_cases baseline : rootMatches o.compression x 0
  · have ep:=ip.trans (congrArg pcAt (if_pos baseline))
    exact ⟨⟨k+3,0,.success,by omega,by decide,by decide,⟨fun _=>⟨0,baseline⟩,fun _=>rfl⟩,cmp.finish (verdict o u true ep)⟩⟩
  · have ep:=ip.trans (congrArg pcAt (if_neg baseline))
    have no : ¬∃ q,rootMatches o.compression x q:=by rintro ⟨q,h⟩;exact baseline h
    exact ⟨⟨k+3,0,.failure,by omega,by decide,by decide,reject_iff no,cmp.finish (verdict o u false ep)⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
