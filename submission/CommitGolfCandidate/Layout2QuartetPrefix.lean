import CommitGolfCandidate.Layout2QuartetLoop
import CommitGolfCandidate.Layout2Prologue
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1200000

theorem guard (s : MachineState) (k len : Nat) (args : Input s k len) (here : s.pc=pc 0) :
    ∃ g, Runs checkImage s g 4 7 ∧ g.pc=(if len<534*k then pc 364 else pc 790) ∧
      g.mem=s.mem ∧ Kept temps s g := by
  obtain ⟨g,run,atG,mem,reg⟩:=ctl_guard s here
  have bound:=args.count;have cap:=args.capacity
  rw [args.card,args.length,show 534#64=addr 534 from rfl,←BitVec.ofNat_mul] at atG
  refine ⟨g,run,?_,mem,?_⟩
  · simpa only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show len<2^64 by omega),
      Nat.mod_eq_of_lt (show k*534<2^64 by omega),decide_eq_true_eq,Nat.mul_comm k 534,Nat.mod_eq_of_lt (show 534*k<2^64 by omega)] using atG
  · intro r free
    have f : Reg.x6≠r := by intro e;subst r;exact free (by decide)
    simp only [reg,if_neg f]

theorem prefix_run (s : MachineState) (k len : Nat) (qs : Selectors)
    (args : Input s k len) (base : s.getReg .x13=addr indicesBase) (here : s.pc=pc 0)
    (indices : Indices s k qs) (long : 534*k≤len) :
    ∃ m h, h≤9+65*k ∧ Runs checkImage s m h (h+3) ∧ m.pc=pc 786 ∧
      Writes s m proofBase (534*k) (payload s k qs) ∧ Kept temps s m := by
  obtain ⟨g,rg,pg,mg,kg⟩:=guard s k len args here
  rw [if_neg (by omega : ¬len<534*k)] at pg
  obtain ⟨a,ra,pa,ma,ka⟩:=ctl_empty g pg
  have eq16 : g.getReg .x16=addr k := (kg _ (by decide)).trans args.card
  rw [eq16] at pa
  have keep : Kept temps s a := fun r fr=>(ka r).trans (kg r fr)
  have cap:=args.capacity;have bound:=args.count
  by_cases zeroK : k=0
  · subst k
    refine ⟨a,5,by decide,rg.thenDo ra,by simpa [addr] using pa,?_,keep⟩
    exact (writes_zero s proofBase _).move rfl (ma.trans mg)
  · have ne : addr k≠0#64 := (addr_ne (by omega) (by decide : 0<2^64)).2 zeroK
    have atA : a.pc=pc 791 := by simpa [ne] using pa
    obtain ⟨b,rb,pb,mb,kb⟩:=ctl_init a atA
    have cb : Cursor b k 0 := by
      constructor
      · simpa [kb,dest,keep _ (by decide : Reg.x15∉temps),args.output]
      · simpa [kb,keep _ (by decide : Reg.x13∉temps),base]
      · simpa [kb,keep _ (by decide : Reg.x16∉temps),args.card]
      · simp [kb,addr]
    have kb' : Kept temps s b := by
      intro r free
      have f : r≠.x8 ∧ r≠.x9 ∧ r≠.x18 ∧ r≠.x19 := by cases r <;> simp_all [temps]
      simp only [kb,if_neg f.1.symm,if_neg f.2.1.symm,if_neg f.2.2.1.symm,if_neg f.2.2.2.symm,keep _ free]
    obtain ⟨m,n,le,rm,pm,wm,km⟩:=traverse bound (by unfold proofBase MEMORY_BYTES;omega) indices
      (k-1) 0 (by omega) b pb cb kb' ((writes_zero s proofBase _).move rfl (mb.trans (ma.trans mg)))
    exact ⟨m,9+n,by omega,by simpa only [show 9+n+3=12+n by omega] using ((rg.thenDo ra).thenDo rb).thenDo rm,pm,wm,km⟩

theorem fuel (k h : Nat) (bound : k≤16777216) (cost : h≤9+65*k) :
    h+prologueSteps k+34359803904≤2^41 := by
  unfold prologueSteps tailSteps Layout2.dispatchCost <;> split_ifs <;> omega

end CommitGolfCandidate.Layout2.Quartet
