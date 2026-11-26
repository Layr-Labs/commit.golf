import CommitGolfCandidate.S5TrialSearch
import CommitGolfCandidate.S5TrialBranch
import CommitGolfCandidate.S5TrialPair
import CommitGolfCandidate.S5TrialPatch
import CommitGolfCandidate.S5TrialPath
import CommitGolfCandidate.S5CapJudgment
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
attribute [local irreducible] readBuffer lookup S5.batchView
theorem trial_cycle (o : Oracle) (x : CheckInput) (old q : Fin 4) (s : MachineState)
    (alone : bothMarked o.compression x=false) (pc : s.pc=pcAt 1125) (regs : TrialRegs o.compression x q s)
    (env : CapEnv x s) (ev : Evidence o.compression x old s) (cache : Cache s (capVal o.compression x old)) :
    ∃ t n c,n≤572 ∧ c≤24 ∧ TrialEnd o x q s t n c := by
  obtain ⟨u,patch,ip,ka,ea,ca⟩:=trial_patch o x old q s _ pc regs ev cache
  have regA:=regs.same ka
  have envA:=env.transport ka ea
  obtain ⟨v,m,c,ms,cs,pair,vp,digest,kb,frame⟩:=trial_pair o x q u ip envA ea regA.addr regA.left regA.right (trial_false_marks alone)
  have eb:=ea.after_node frame (by decide) (by decide) (by decide)
  have cb:=ca.write (h:=0) (i:=170) (by decide) (by decide) (capVal o.compression x q 0 170) digest frame
  obtain ⟨w,k,ks,path,wp,cw,ew,kc⟩:=trial_path o x old q v vp (envA.transport kb eb) eb cb
  have keep:=(ka.trans kb).trans kc
  have envW:=env.transport keep ew
  obtain ⟨t,l,ls,cmp,tp,mem,kd⟩:=root_judge o x w true q wp envW cw
  have et:=ew.same mem
  exact ⟨t,3+m+k+l,c+8,by omega,by omega,⟨by simpa only [Nat.zero_add,Nat.add_zero] using ((patch.trans pair).trans path).trans cmp,
    tp,regs.same (keep.trans kd),envW.transport kd et,et,cw.same mem⟩⟩

theorem cap_judgment : CapJudgment:=cap_of_cycles trial_cycle
end CommitGolfCandidate.S5Machine.Check
