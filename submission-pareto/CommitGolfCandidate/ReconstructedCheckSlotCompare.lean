import CommitGolfCandidate.ReconstructedCheckSlotWords

namespace CommitGolfCandidate.Reconstruction.CheckSlotCompare
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckRecorded CheckRecordAccess CheckSlotWords
open TwoPermutationPrototype.RV64
set_option maxRecDepth 15000
set_option maxHeartbeats 1400000
abbrev W:=BitVec.ofNat 64

def EqualAt (s : MachineState) (k : Nat) (j : Fin 4) := s.getReg (operand j)=s.getMem (point k j)
deriving instance Decidable for EqualAt

def Agree (s : MachineState) (k : Nat) (j : Fin 4) := ∀ l : Fin 4,j.val≤l.val→EqualAt s k l
deriving instance Decidable for Agree

theorem same {s t : MachineState} (k : Nat) (small : k<1024)
    (reg : ∀ r,reserve r→t.getReg r=s.getReg r) (mem : Mem s t) (l : Fin 4) :
    EqualAt t k l ↔ EqualAt s k l := by
  unfold EqualAt point;rw [reg _ ((by decide : ∀ i : Fin 4,reserve (operand i)) l),
    mem (capWord k l) (by have h:=l.isLt;unfold capWord;omega)]

theorem loop (o : Oracle) (s : MachineState) (k : Nat) (small : k<1024) (n : Nat) (i : Fin 4) (order : n+i.val=3)
    (loc : s.pc=CommitBlocks.addr (loadAt i)) (p : s.getReg .x16=point k 0) :
    ∃ t m,m≤2*(n+1)+1 ∧ Segment o m s t [] ∧
      t.pc=(if Agree s k i then CommitBlocks.addr 109 else CommitBlocks.addr 57) ∧
      (∀ r,reserve r→t.getReg r=s.getReg r) ∧ Mem s t := by
  induction n generalizing s i with
  | zero=>
    have last : i.val=3:=by omega
    obtain ⟨u,run,pos,regs,mem,_⟩:=one o s k i small loc p
    change u.pc=(if EqualAt s k i then _ else _) at pos
    have all : Agree s k i ↔ EqualAt s k i:=by
      refine ⟨fun h=>h i (by omega),?_⟩
      intro h j less;have e : j=i:=Fin.ext (by have:=j.isLt;omega);exact e ▸ h
    by_cases eq : EqualAt s k i
    · rw [ite_eq_left eq] at pos;refine ⟨u,2,by decide,run,?_,regs,mem⟩
      simpa only [ite_eq_left (all.mpr eq),okAt,last,ite_true] using pos
    · rw [ite_eq_right eq] at pos
      have jmp:=CheckBranch.jump o u 408 57 2095748 (by decide) (by simpa [failAt,last] using pos) rfl (by decide)
      exact ⟨u.setPC (CommitBlocks.addr 57),3,by decide,by simpa using compose run jmp,by rw [ite_eq_right (fun h=>eq (all.mp h))];rfl,regs,mem⟩
  | succ n ih=>
    have early : i.val<3:=by omega
    obtain ⟨u,run,pos,regs,mem,ptr⟩:=one o s k i small loc p
    change u.pc=(if EqualAt s k i then _ else _) at pos
    by_cases eq : EqualAt s k i
    · rw [ite_eq_left eq] at pos
      let j : Fin 4:=⟨i.val+1,by omega⟩
      have jloc : u.pc=CommitBlocks.addr (loadAt j):=by
        rw [pos,okAt,ite_eq_right (by omega)];congr 1 <;> (try unfold loadAt) <;> (try dsimp [j]) <;> omega
      obtain ⟨t,m,lim,rest,tpc,regT,memT⟩:=ih u j (by dsimp [j];omega) jloc (ptr early)
      have rel : Agree u k j ↔ Agree s k i:=by
        constructor
        · intro ok l ord
          by_cases atI : l=i
          · exact atI ▸ eq
          · have ne : l.val≠i.val:=fun e=>atI (Fin.ext e)
            exact (same k small regs mem l).mp (ok l (by change i.val+1≤_;omega))
        · intro ok l ord;exact (same k small regs mem l).mpr (ok l (by change i.val+1≤l.val at ord;omega))
      exact ⟨t,2+m,by omega,by simpa using compose run rest,by simpa only [rel] using tpc,
        fun r h=>(regT r h).trans (regs r h),fun w h=>(memT w h).trans (mem w h)⟩
    · rw [ite_eq_right eq] at pos
      have bad : ¬ Agree s k i:=fun h=>eq (h i (by omega))
      exact ⟨u,2,by omega,run,by simpa only [ite_eq_right bad,failAt,ite_eq_right (show i.val ≠ 3 by omega)] using pos,regs,mem⟩

theorem positive (o : Oracle) (s : MachineState) (k : Nat) (room : k<1024) (pos : s.pc=CommitBlocks.addr 398)
    (shift : s.getReg .x23=W (32*k)) :
    ∃ t n,n≤11 ∧ Segment o n s t [] ∧
      t.pc=(if ∀ i : Fin 4,EqualAt s k i then CommitBlocks.addr 109 else CommitBlocks.addr 57) ∧
      (∀ r,reserve r→t.getReg r=s.getReg r) ∧ Mem s t := by
  obtain ⟨u,a,atU,pu,regs,mem⟩:=CheckSlotWords.begin o s k pos shift
  obtain ⟨t,n,lim,b,pt,tr,tm⟩:=loop o u k room 3 0 (by decide) atU pu
  have iff : Agree u k 0 ↔ ∀ i : Fin 4,EqualAt s k i:=by
    simp only [Agree,Fin.val_zero,Nat.zero_le,forall_const];exact forall_congr' (same k room regs mem)
  exact ⟨t,2+n,by omega,by simpa using compose a b,by simpa only [iff] using pt,
    fun r h=>(tr r h).trans (regs r h),fun w h=>(tm w h).trans (mem w h)⟩

end CommitGolfCandidate.Reconstruction.CheckSlotCompare
