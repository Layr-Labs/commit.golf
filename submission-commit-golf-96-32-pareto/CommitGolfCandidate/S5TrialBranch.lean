import CommitGolfCandidate.S5RootJudge
import CommitGolfCandidate.S5TrialPatchSetup
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

theorem CapEnv.transport {H x q s t} (env : CapEnv x s) (keep : CapKeeps s t) (ev : Evidence H x q t) : CapEnv x t :=
  ⟨(keep _ (by decide)).trans env.root,(keep _ (by decide)).trans env.row,(keep _ (by decide)).trans env.chain,ev.root⟩

def trialLatchPC (q : Fin 4) :=if q.val+1<4 then 1125 else 2333
def trialLatchState (s : MachineState) (q : Fin 4):=(s.setReg .x19 (W (q.val+1))).setPC (pcAt (trialLatchPC q))
theorem trial_latch (o : Oracle) (x : CheckInput) (q : Fin 4) (s : MachineState) (pc : s.pc=pcAt 1275) (r : TrialRegs o.compression x q s) :
  ∃ n,n≤3 ∧ Flow o s (trialLatchState s q) n 0 := by
  let u:=(s.setReg .x19 (W (q.val+1))).setPC (pcAt 1276)
  have inc:=imm_step o s 1275 .x19 .x19 1 (W (q.val+1)) pc (known (by decide +kernel)) ((congrArg (·+signExtend12 1) r.trial).trans (BitVec.ofNat_add q.val 1).symm)
  have less : Rel.lt.test (u.getReg .x19) (u.getReg .x20)=decide (q.val+1<4):=by
    change BitVec.ult (W (q.val+1)) (s.getReg .x20)=_
    rw [r.limit];exact (by decide +kernel : ∀ z : Fin 4,BitVec.ult (W (z.val+1)) (W 4)=decide (z.val+1<4)) q
  have test:=branch o u 1276 1125 .lt .x19 .x20 (by decide +kernel) rfl _ less
  by_cases inside : q.val+1<4
  · rw [decide_eq_true inside] at test
    exact ⟨2,by decide,by unfold trialLatchState trialLatchPC;rw [if_pos inside];exact inc.trans test⟩
  · rw [decide_eq_false inside] at test
    let v:=u.setPC (pcAt 1277)
    have fail:=jump o v 1277 2333 .x0 (by decide +kernel) rfl
    exact ⟨3,by decide,by unfold trialLatchState trialLatchPC;rw [if_neg inside];exact (inc.trans test).trans fail⟩

theorem latch_regs {H x q s} (r : TrialRegs H x q s) (inside : q.val+1<4) :
    TrialRegs H x ⟨q.val+1,inside⟩ (trialLatchState s q) :=⟨r.addr,r.baseWord,rfl,r.limit,r.left,r.right⟩
theorem latch_env {x s} (env : CapEnv x s) (q : Fin 4) : CapEnv x (trialLatchState s q) :=⟨env.root,env.row,env.chain,env.read⟩

def tailMatches (H : Compression) (x : CheckInput) (n : Nat) :=∃ q : Fin 4,n≤q.val ∧ rootMatches H x q
theorem tail_of_ne {H x q} (no : ¬rootMatches H x q) : tailMatches H x (q.val+1) ↔ tailMatches H x q.val :=by
  constructor
  · rintro ⟨i,h,ok⟩;exact ⟨i,by omega,ok⟩
  · rintro ⟨i,h,ok⟩
    have ne : i.val≠q.val:=fun a=>no (Fin.ext a ▸ ok)
    exact ⟨i,by omega,ok⟩

theorem trial_false_marks {H x} (h : bothMarked H x=false) : lookup H x 128 340=none ∨ lookup H x 128 341=none := by
  unfold bothMarked at h
  cases e : lookup H x 128 340 <;> cases f : lookup H x 128 341 <;> simp_all
theorem trial_true_marks {H x} (h : bothMarked H x=true) : ∀ q,rootMatches H x q ↔ rootMatches H x 0 := by
  unfold bothMarked at h
  cases e : lookup H x 128 340 with
  | none=>simp [e] at h
  | some a=>
    cases f : lookup H x 128 341 with
    | none=>simp [f] at h
    | some b=>exact two_marks_same H x a b e f
end CommitGolfCandidate.S5Machine.Check
