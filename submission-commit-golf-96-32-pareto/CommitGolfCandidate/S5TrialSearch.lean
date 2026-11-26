import CommitGolfCandidate.S5CapJudgment
import CommitGolfCandidate.S5TrialBranch
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
structure TrialEnd (o : Oracle) (x : CheckInput) (q : Fin 4) (s t : MachineState) (n c : Nat) : Prop where
  run : Flow o s t n c
  pc : t.pc=pcAt (if rootMatches o.compression x q then 2330 else 1275)
  regs : TrialRegs o.compression x q t
  env : CapEnv x t
  evidence : Evidence o.compression x q t
  cache : Cache t (capVal o.compression x q)

def TrialCycle := ∀ (o : Oracle) (x : CheckInput) (old q : Fin 4) (s : MachineState)
    (alone : bothMarked o.compression x=false) (pc : s.pc=pcAt 1125) (regs : TrialRegs o.compression x q s)
    (env : CapEnv x s) (ev : Evidence o.compression x old s) (cache : Cache s (capVal o.compression x old)),
    ∃ t n c,n≤572 ∧ c≤24 ∧ TrialEnd o x q s t n c

theorem trial_search (cycle : TrialCycle) (o : Oracle) (x : CheckInput) (old q : Fin 4) (s : MachineState) (n : Nat) (rem : q.val+n=3)
    (alone : bothMarked o.compression x=false) (pc : s.pc=pcAt 1125) (regs : TrialRegs o.compression x q s)
    (env : CapEnv x s) (ev : Evidence o.compression x old s) (cache : Cache s (capVal o.compression x old)) :
    Outcome o s (tailMatches o.compression x q.val) (580*(n+1)) (24*(n+1)) := by
  induction n generalizing old q s with
  | zero=>
    obtain ⟨u,k,c,ks,cs,h⟩:=cycle o x old q s alone pc regs env ev cache
    by_cases ok : rootMatches o.compression x q
    · have end_:=verdict o u true (h.pc.trans (congrArg pcAt (if_pos ok)))
      exact ⟨⟨k+3,c,.success,by omega,cs,by decide,⟨fun _=>⟨q,le_rfl,ok⟩,fun _=>rfl⟩,h.run.finish end_⟩⟩
    · obtain ⟨uSteps,lim,latch⟩:=trial_latch o x q u (h.pc.trans (congrArg pcAt (if_neg ok))) h.regs
      have last : ¬q.val+1<4:=by omega
      have ep : (trialLatchState u q).pc=pcAt 2333:=congrArg pcAt (if_neg last)
      have no : ¬tailMatches o.compression x q.val:=by
        rintro ⟨i,after_,good⟩
        have e : i=q:=Fin.ext (by have bound:=i.isLt;omega)
        exact ok (e ▸ good)
      exact ⟨⟨k+uSteps+3,c,.failure,by omega,cs,by decide,reject_iff no,(h.run.trans latch).finish (verdict o _ false ep)⟩⟩
  | succ n ih=>
    obtain ⟨u,k,c,ks,cs,h⟩:=cycle o x old q s alone pc regs env ev cache
    by_cases ok : rootMatches o.compression x q
    · have end_:=verdict o u true (h.pc.trans (congrArg pcAt (if_pos ok)))
      exact ⟨⟨k+3,c,.success,by omega,by omega,by decide,⟨fun _=>⟨q,le_rfl,ok⟩,fun _=>rfl⟩,h.run.finish end_⟩⟩
    · have bound : q.val+1<4:=by omega
      let next : Fin 4:=⟨q.val+1,bound⟩
      obtain ⟨l,ls,lat⟩:=trial_latch o x q u (h.pc.trans (congrArg pcAt (if_neg ok))) h.regs
      let v:=trialLatchState u q
      have vp : v.pc=pcAt 1125:=congrArg pcAt (if_pos bound)
      have r : next.val+n=3:=by dsimp [next];omega
      have end_:=ih q next v r vp (latch_regs h.regs bound) (latch_env h.env q) (h.evidence.same rfl) (h.cache.same rfl)
      exact (Outcome.prefix (h.run.trans lat) end_).weaken (tail_of_ne ok) (by omega) (by omega)

theorem cap_of_cycles (cycle : TrialCycle) : CapJudgment := by
  intro o x s pc env ev cache
  obtain ⟨u,k,lim,cmp,ip,mem,keep⟩:=root_judge o x s false 0 pc env cache
  by_cases baseline : rootMatches o.compression x 0
  · have ep:=ip.trans (congrArg pcAt (if_pos baseline))
    exact ⟨⟨k+3,0,.success,by omega,by decide,by decide,⟨fun _=>⟨0,baseline⟩,fun _=>rfl⟩,cmp.finish (verdict o u true ep)⟩⟩
  · have eu:=ev.same mem
    obtain ⟨v,l,ls,setup,vp,r,vm,kp⟩:=trial_setup o x u (ip.trans (congrArg pcAt (if_neg baseline))) eu
    have front:=cmp.trans setup
    cases marks : bothMarked o.compression x
    · have ep : v.pc=pcAt 1125:=by rw [marks] at vp;exact vp
      have et:=eu.same vm
      have envU:=env.transport keep eu
      have envV : CapEnv x v:=⟨(kp _ (by decide)).trans envU.root,(kp _ (by decide)).trans envU.row,(kp _ (by decide)).trans envU.chain,et.root⟩
      have loop:=trial_search cycle o x 0 1 v 2 (by decide) marks ep r envV et ((cache.same mem).same vm)
      have eq : tailMatches o.compression x 1 ↔ ∃ q,rootMatches o.compression x q:=by
        constructor
        · rintro ⟨q,_,h⟩;exact ⟨q,h⟩
        · rintro ⟨q,h⟩
          have ne : q.val≠0:=fun e=>baseline ((Fin.ext (show q.val=(0 : Fin 4).val from e)) ▸ h)
          exact ⟨q,by omega,h⟩
      exact (Outcome.prefix front loop).weaken eq (by omega) (by decide)
    · have ep : v.pc=pcAt 2333:=by rw [marks] at vp;exact vp
      have no : ¬∃ q,rootMatches o.compression x q:=by rintro ⟨q,h⟩;exact baseline ((trial_true_marks marks q).mp h)
      exact ⟨⟨k+l+3,0,.failure,by omega,by decide,by decide,reject_iff no,front.finish (verdict o v false ep)⟩⟩

end CommitGolfCandidate.S5Machine.Check
