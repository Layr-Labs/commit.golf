import CommitGolfCandidate.TruncSchedule
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 160000

def shifted (s : MachineState) :=
  (s.setReg .x21 (s.getReg .x21-s.getReg .x24)).setReg .x22 (s.getReg .x22-1536)

theorem shiftSame (s : MachineState) (pc : Word) : (parentNextState s).setPC pc=(shifted s).setPC pc := rfl

private theorem shift2 (s : MachineState) (i : Nat) (here : i=689 ∨ i=930) (pc : s.pc=loc i) :
    Runs (submission.image .commit) s ((shifted s).setPC (loc (i+2))) 2 2 := by
  let m:=(s.setReg .x21 (s.getReg .x21-s.getReg .x24)).setPC (loc (i+1))
  have e1 : Runs (submission.image .commit) s m 1 1 := by
    apply one i _ _ (.SUB .x21 .x21 .x24) (by omega) pc (by rcases here with rfl|rfl <;> rfl) _ rfl
    simp [ordinaryStep,m,memAccess,memoryArgumentsValid,execInstrBr,pc,loc,MachineState.setPC,←BitVec.ofNat_add]
    try congr 1 <;> omega
  have e2 : Runs (submission.image .commit) m ((shifted s).setPC (loc (i+2))) 1 1 := by
    apply one (i+1) _ _ (.ADDI .x22 .x22 2560) (by omega) rfl (by rcases here with rfl|rfl <;> rfl) _ rfl
    rcases here with rfl|rfl <;>
      simp [ordinaryStep,memAccess,memoryArgumentsValid,execInstrBr,m,shifted,MachineState.setPC,MachineState.setReg,
        MachineState.getReg,loc,signExtend12,BitVec.sub_eq_add_neg]
  exact chain e1 e2

private theorem branchAt (s : MachineState) (i j : Nat) (a b : Reg) (off : BitVec 13) (bound : i<2048)
    (pc : s.pc=loc i) (code : ((submission.image .commit).code[i]?).bind decodeInstruction=some (.base (.BNE a b off)))
    (target : (if s.getReg a≠s.getReg b then loc i+signExtend13 off else loc i+4)=loc j) :
    Runs (submission.image .commit) s (s.setPC (loc j)) 1 1 := by
  apply one i _ _ (.BNE a b off) bound pc code _ rfl
  by_cases eq : s.getReg a=s.getReg b
  · simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,eq] at target ⊢;rw [target]
  · simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,eq] at target ⊢;rw [target]

private theorem word_ne {m n : Nat} (bm : m<2^64) (bn : n<2^64) (ne : m≠n) :
    BitVec.ofNat 64 m≠BitVec.ofNat 64 n := by
  intro e;have h:=congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt bm,Nat.mod_eq_of_lt bn] at h;exact ne h

private theorem lowerLatch (s : MachineState) (q : Nat) (lo : threshold≤q) (small : q<2^24) (mult : q%32=0)
    (pc : s.pc=loc 689) (f : RegFrame q s) :
    Runs (submission.image .commit) s (nextState q s) (suffixSteps q) (suffixSteps q) := by
  have step:=shift2 s 689 (Or.inl rfl) pc
  let m:=(shifted s).setPC (loc 691)
  have pos : 0<q := by unfold threshold at lo;omega
  have p:=f.pointers;rw [show q/32=(q-1)/32+1 by omega] at p
  have pp:=dropPtr ((q-1)/32) p
  have v : m.getReg .x22=BitVec.ofNat 64 (heapBase+1536*((q-1)/32)) := pp.dst
  have w : m.getReg .x17=BitVec.ofNat 64 switchPtr :=
    ((parent_next_registers s).2.2.2 .x17 (by decide) (by decide)).trans f.switch
  have go (j : Nat) := branchAt m 691 j .x22 .x17 7800 (by decide) rfl (by rfl)
  have neq2 : q≠2 := by unfold threshold at lo;omega
  by_cases cut : q=threshold
  · have e : m.getReg .x22=m.getReg .x17 := by rw [v,w,cut];rfl
    have j:=go (j:=692) (by rw [if_neg (not_not_intro e)];decide)
    have k:=jumpAt (submission.image .commit) (m.setPC (loc 692)) 692 802 440 (by decide) rfl (by rfl) (by decide)
    rw [suffixSteps,if_pos mult,if_pos (Or.inl cut),nextState,if_pos mult,shiftSame,cut]
    exact chain (chain step j) k
  · have ne : m.getReg .x22≠m.getReg .x17 := by
      rw [v,w]
      apply word_ne
      · change 4294971424+1536*((q-1)/32)<2^64;omega
      · decide
      · change 4294971424+1536*((q-1)/32)≠4294971424+48*(4194304-32)
        unfold threshold at lo cut;omega
    have j:=go (j:=593) (by rw [if_pos ne];decide)
    have nw:=afterLatch q pos mult
    rw [if_pos (by omega : threshold<q)] at nw
    rw [suffixSteps,if_pos mult,if_neg (not_or.mpr ⟨cut,neq2⟩),nextState,if_pos mult,shiftSame,nw]
    exact chain (a:=2) (b:=2) (c:=1) (d:=1) step j

private theorem upperLatch (s : MachineState) (q : Nat) (hi : q<threshold) (pos : 0<q) (mult : q%32=0)
    (pc : s.pc=loc 930) (f : RegFrame q s) :
    Runs (submission.image .commit) s (nextState q s) (suffixSteps q) (suffixSteps q) := by
  have step:=shift2 s 930 (Or.inr rfl) pc
  let m:=(shifted s).setPC (loc 932)
  have p:=f.pointers;rw [show q/32=(q-1)/32+1 by omega] at p
  have pp:=dropPtr ((q-1)/32) p
  have v : m.getReg .x22=BitVec.ofNat 64 (heapBase+1536*((q-1)/32)) := pp.dst
  have w : m.getReg .x9=BitVec.ofNat 64 heapBase := pp.heap
  have go (j : Nat) := branchAt m 932 j .x22 .x9 7672 (by decide) rfl (by rfl)
  have nw:=afterLatch q pos mult
  rw [if_neg (by omega : ¬threshold<q)] at nw
  rw [suffixSteps,if_pos mult,if_neg (by omega : ¬(q=threshold ∨ q=2)),nextState,if_pos mult,shiftSame,nw]
  by_cases last : 32<q
  · have ne : m.getReg .x22≠m.getReg .x9 := by
      rw [v,w];apply word_ne <;> unfold heapBase threshold at * <;> omega
    rw [if_pos last];exact chain (a:=2) (b:=2) (c:=1) (d:=1) step (go (j:=802) (by rw [if_pos ne];decide))
  · have eq : q=32 := by omega
    have e : m.getReg .x22=m.getReg .x9 := by rw [v,w,eq];rfl
    rw [if_neg last];exact chain (a:=2) (b:=2) (c:=1) (d:=1) step (go (j:=933) (by rw [if_neg (not_not_intro e)];decide))

theorem runSuffix (s : MachineState) (q : Nat) (pos : 0<q) (small : q<2^24)
    (pc : s.pc=loc (word q+bodySteps q)) (f : RegFrame q s) :
    Runs (submission.image .commit) s (nextState q s) (suffixSteps q) (suffixSteps q) := by
  by_cases wrap : q%32=0
  · rw [beforeLatch q pos wrap] at pc
    by_cases low : threshold≤q
    · rw [if_pos low] at pc;exact lowerLatch s q low small wrap pc f
    · rw [if_neg low] at pc;exact upperLatch s q (by omega) pos wrap pc f
  · rw [suffixSteps,if_neg wrap,nextState,if_neg wrap]
    by_cases near : q=2
    · subst q;exact jumpAt (submission.image .commit) s 1053 782 2096068 (by decide) pc (by rfl) (by decide)
    · have neq : q≠threshold := fun h=>wrap (h ▸ (by decide : threshold%32=0))
      rw [if_neg (not_or.mpr ⟨neq,near⟩)]
      rw [straightNext q pos wrap near] at pc
      have eq : s.setPC (loc (word (q-1)))=s := by rw [←pc];rfl
      rw [eq];exact runRefl _ s
end CommitGolfCandidate.Trunc
