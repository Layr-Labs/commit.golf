import CommitGolfCandidate.ReconstructedCheckRootPlan

namespace CommitGolfCandidate.Reconstruction.CheckRoot
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues CheckRecorded CheckParentRun CheckRootPlan
set_option maxRecDepth 16000
set_option maxHeartbeats 1150000

abbrev W := BitVec.ofNat 64

def env (s : MachineState) : Env := ⟨s,fun _=>0,rfl,fun _ _=>0⟩

theorem layout (s : MachineState) : Layout (env s) CheckRootPlan.table := by
  constructor
  · intro a h
    change decide (_ ∧ _ ∧ _)=true at h;rw [decide_eq_true_eq] at h
    have zero : physical (env s) a=a.offset := by change 0#64+a.offset=_;exact BitVec.zero_add _
    rw [zero];change (decide (a.offset.toNat+8≤MEMORY_BYTES) && decide (a.offset.toNat%8=0))=true
    rw [Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
    obtain ⟨_,align,room⟩:=h
    exact ⟨by unfold CheckRootPlan.cap commitment at room;unfold MEMORY_BYTES;omega,align⟩
  · intro a b ha hb eq
    change decide (_ ∧ _ ∧ _)=true at ha hb;rw [decide_eq_true_eq] at ha hb
    simp only [physical,env,BitVec.zero_add] at eq
    cases a;cases b;simp_all
  · intro a w h;cases h

def Entry (s : MachineState) (i : Fin 4) := s.pc=CommitBlocks.addr (CheckRootPlan.begin i) ∧
  (i.val ≠ 0 → s.getReg .x11=W commitment ∧ s.getReg .x12=W (if i.val=1 then CheckRootPlan.cap-32 else CheckRootPlan.cap))

theorem matched (s : MachineState) (i : Fin 4) (h : Entry s i) : Matches (env s) (CheckRootPlan.start i) s := by
  refine ⟨h.1,?_,fun _=>rfl⟩
  intro r
  by_cases first : i.val=0
  · cases r <;> simp [State.get,CheckRootPlan.start,first,Term.val,env,MachineState.getReg]
  · have args:=h.2 first
    cases r <;> simp [State.get,CheckRootPlan.start,first,Term.val,env,MachineState.getReg] at *
    · exact args.1
    · exact args.2

/-- The two words compared at the indicated position in the root digest. -/
def EqualAt (s : MachineState) (i : Fin 4) : Prop :=
  s.getMem (W (CheckRootPlan.cap+8*i.val))=s.getMem (W (commitment+8*i.val))
deriving instance Decidable for EqualAt

def Agree (s : MachineState) (i : Fin 4) := ∀ j : Fin 4, i.val≤j.val→EqualAt s j
deriving instance Decidable for Agree

private theorem stage (o : Oracle) (s : MachineState) (i : Fin 4) (h : Entry s i) :
    ∃ t, Segment o ((code i).length+1) s t [] ∧
      t.pc=(if EqualAt s i then CommitBlocks.addr (guardAt i+1) else CommitBlocks.addr 57) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ r ∈ keep,t.getReg r=s.getReg r) ∧
      (i.val<3 → t.getReg .x11=W commitment ∧ t.getReg .x12=W (if i.val=0 then CheckRootPlan.cap-32 else CheckRootPlan.cap)) :=
  CheckRootPlan.positive o (env s) (layout s) i s (matched s i h)

private theorem cost : ∀ i : Fin 4, (code i).length+1≤7 := by decide
private theorem nextPC : ∀ i j : Fin 4, j.val=i.val+1→guardAt i+1=CheckRootPlan.begin j := by decide

private theorem loop (o : Oracle) (rem : Nat) (s : MachineState) (i : Fin 4) (count : i.val+rem=3) (atStart : Entry s i) :
    ∃ t n, n≤7*(rem+1) ∧ Segment o n s t [] ∧ t.pc=(if Agree s i then CommitBlocks.addr 657 else CommitBlocks.addr 57) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ r ∈ keep, t.getReg r=s.getReg r) := by
  induction rem generalizing s i with
  | zero =>
    obtain ⟨u,pre,pos,memory,regs,_⟩:=stage o s i atStart
    have endAt : i=3:=Fin.ext (by omega)
    have eqv : EqualAt s i ↔ Agree s i := by
      constructor
      · intro same j order;have ij : j=i:=Fin.ext (by omega);simpa only [ij] using same
      · intro all;exact all i (Nat.le_refl _)
    refine ⟨u,_,by simpa using cost i,pre,?_,memory,regs⟩
    by_cases yes : EqualAt s i
    · rw [pos,if_pos yes,if_pos (eqv.mp yes),endAt];rfl
    · rw [pos,if_neg yes,if_neg (fun h=>yes (eqv.mpr h))]
  | succ k ih =>
    obtain ⟨u,pre,pos,memory,regs,next⟩:=stage o s i atStart
    by_cases same : EqualAt s i
    · rw [if_pos same] at pos
      have earlier : i.val<3:=by omega
      let j : Fin 4:=⟨i.val+1,by omega⟩
      have val : j.val=i.val+1:=rfl
      have neu : Entry u j := by
        refine ⟨pos.trans (congrArg CommitBlocks.addr (nextPC i j val)),?_⟩
        intro _;obtain ⟨l,r⟩:=next earlier;refine ⟨l,r.trans ?_⟩
        by_cases first : i.val=0
        · rw [if_pos first,if_pos (by omega : j.val=1)]
        · rw [if_neg first,if_neg (by omega : j.val≠1)]
      obtain ⟨t,n,small,tail,final,mem,reg⟩:=ih u j (by omega) neu
      have eqv : Agree u j ↔ Agree s i := by
        constructor
        · intro ok a order;by_cases cur : a=i
          · simpa only [cur] using same
          · have later : j.val≤a.val:=by have ne : a.val≠i.val:=fun h=>cur (Fin.ext h);omega
            have h:=ok a later;unfold EqualAt at h ⊢;simpa only [memory] using h
        · intro ok a order;have h:=ok a (by omega);unfold EqualAt at h ⊢;simpa only [memory] using h
      exact ⟨t,(code i).length+1+n,by have k0:=cost i;omega,by simpa using compose pre tail,by simpa only [eqv] using final,
        fun p=>(mem p).trans (memory p),fun r hr=>(reg r hr).trans (regs r hr)⟩
    · have bad : ¬ Agree s i:=fun h=>same (h i (Nat.le_refl _))
      exact ⟨u,(code i).length+1,by have c:=cost i;omega,pre,by simpa only [if_neg same,if_neg bad] using pos,memory,regs⟩

/-- The actual four 64-bit comparisons accept precisely a matching 256-bit root. -/
theorem positive (o : Oracle) (s : MachineState) (pos : s.pc=CommitBlocks.addr 640) :
    ∃ t n, n≤28 ∧ Segment o n s t [] ∧
      t.pc=(if ∀ j : Fin 4,EqualAt s j then CommitBlocks.addr 657 else CommitBlocks.addr 57) ∧
      (∀ p,t.getMem p=s.getMem p) ∧ (∀ r ∈ keep,t.getReg r=s.getReg r) := by
  have initial : Entry s 0 := ⟨pos,by intro h;exact False.elim (h rfl)⟩
  simpa only [Agree,Fin.val_zero,Nat.zero_le,forall_const] using loop o 3 s 0 (by decide) initial

end CommitGolfCandidate.Reconstruction.CheckRoot
