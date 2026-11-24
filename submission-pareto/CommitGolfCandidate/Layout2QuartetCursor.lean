import CommitGolfCandidate.Layout2QuartetDispatch

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 1300000
abbrev indicesBase : Nat := 9395245088
def dest (j : Nat) := proofBase+8*((534*j)/8)
structure Cursor (s : MachineState) (k j : Nat) : Prop where
  dst : s.getReg .x8=addr (dest j)
  ix : s.getReg .x9=addr (indicesBase+8*j)
  left : s.getReg .x18=addr (k-j)
  phase : s.getReg .x19=addr (j%4)

theorem Cursor.lift {s t k j} (h : Cursor s k j)
    (same : ∀ r, r=.x8 ∨ r=.x9 ∨ r=.x18 ∨ r=.x19 → t.getReg r=s.getReg r) : Cursor t k j :=
  ⟨(same _ (by decide)).trans h.dst,(same _ (by decide)).trans h.ix,
   (same _ (by decide)).trans h.left,(same _ (by decide)).trans h.phase⟩

theorem low2 (n : Nat) : addr n &&& 3#64=addr (n%4) := by
  rw [show 3#64=addr 3 from rfl,←BitVec.ofNat_and]
  congr 1
  exact Nat.and_two_pow_sub_one_eq_mod n 2

theorem decWord (n : Nat) (nz : 0<n) : addr n+18446744073709551615#64=addr (n-1) := by
  rw [show n=(n-1)+1 by omega] <;> simp [addr,BitVec.ofNat_add,BitVec.add_assoc]

theorem remaining {s k j} (c : Cursor s k j) (hj : j<k) (bound : k≤16777216) (here : s.pc=pc 992) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(if j+1=k then pc 786 else pc 994) ∧ t.mem=s.mem ∧
      t.getReg .x18=addr (k-(j+1)) ∧ ∀ r,r≠.x18 → t.getReg r=s.getReg r := by
  obtain ⟨t,ran,atT,mem,reg⟩:=ctl_tail s here
  rw [c.left,show signExtend12 4095=18446744073709551615#64 from rfl,decWord _ (by omega),show k-j-1=k-(j+1) by omega] at atT reg
  refine ⟨t,ran,?_,mem,by simpa using reg .x18,?_⟩
  · by_cases last : j+1=k
    · simpa [last,addr] using atT
    · have ne : addr (k-(j+1))≠0#64 := by
        apply (addr_ne (by omega) (by decide : 0<2^64)).2;omega
      simpa [last,ne] using atT
  · intro r h;simpa [Ne.symm h] using reg r

theorem bump {s k j} (dst : s.getReg .x8=addr (dest j)) (ix : s.getReg .x9=addr (indicesBase+8*j))
    (left : s.getReg .x18=addr (k-(j+1))) (phase : s.getReg .x19=addr (j%4)) (here : s.pc=pc 994) :
    ∃ t n, n≤7 ∧ Runs checkImage s t n n ∧ t.pc=pc 795 ∧ t.mem=s.mem ∧ Cursor t k (j+1) ∧ Kept temps s t := by
  obtain ⟨a,runA,pcA,memA,regA⟩:=ctl_bump s here
  have mid : ∃ u n, n≤4 ∧ Runs checkImage s u n n ∧ u.pc=pc 998 ∧ u.mem=s.mem ∧
      u.getReg .x8=addr (dest (j+1)) ∧ u.getReg .x9=addr (indicesBase+8*(j+1)) ∧
      ∀ r,r≠.x8 → r≠.x9 → u.getReg r=s.getReg r := by
    have ixA : a.getReg .x9=addr (indicesBase+8*(j+1)) := by
      rw [regA];simp only [reduceCtorEq,ite_false,ite_true,ix,show 8#64=addr 8 from rfl,addr_add] <;> congr 1 <;> omega
    have dstA : a.getReg .x8=addr (dest j+536) := by
      rw [regA];simp only [ite_true,dst,show 536#64=addr 536 from rfl,addr_add]
    by_cases special : j%4=0
    · have atA : a.pc=pc 997 := by simpa [phase,special,addr] using pcA
      obtain ⟨u,ran,atU,memU,regs⟩:=ctl_shortStride a atA
      refine ⟨u,4,by decide,runA.thenDo ran,atU,memU.trans memA,?_,?_,?_⟩
      · rw [regs,if_pos rfl,dstA]
        have eq : dest j+536=dest (j+1)+8 := by unfold dest;omega
        rw [eq,←addr_add,show signExtend12 4088=18446744073709551608#64 from rfl];simp [addr,BitVec.add_assoc]
      · simpa [regs] using ixA
      · intro r f g;simp only [regs,regA,if_neg f.symm,if_neg g.symm]
    · have nz : addr (j%4)≠0#64 := (addr_ne (by omega) (by decide : 0<2^64)).2 special
      have atA : a.pc=pc 998 := by simpa [phase,nz] using pcA
      refine ⟨a,3,by decide,runA,atA,memA,?_,ixA,?_⟩
      · rw [dstA];congr 1;unfold dest;rw [phase_base,phase_base];unfold phaseBase;split_ifs <;> omega
      · intro r f g;simp only [regA,if_neg f.symm,if_neg g.symm]
  obtain ⟨u,n,count,ran,atU,memU,baseU,ixU,fixed⟩:=mid
  obtain ⟨t,runT,pcT,memT,regT⟩:=ctl_next u atU
  refine ⟨t,n+3,by omega,ran.thenDo runT,pcT,memT.trans memU,⟨?_,?_,?_,?_⟩,?_⟩
  · simpa [regT] using baseU
  · simpa [regT] using ixU
  · simpa [regT,fixed _ (by decide : Reg.x18≠.x8) (by decide : Reg.x18≠.x9)] using left
  · rw [regT,if_pos rfl,fixed _ (by decide) (by decide),phase,show 1#64=addr 1 from rfl,addr_add,low2];congr 1;omega
  · intro r free
    have f : r≠.x8 ∧ r≠.x9 ∧ r≠.x19 := by cases r <;> simp_all [temps]
    simp only [regT,if_neg f.2.2.symm,fixed _ f.1 f.2.1]

end CommitGolfCandidate.Layout2.Quartet
