import CommitGolfCandidate.GroupOpenLatch
import CommitGolfCandidate.GroupedSaltMap
import CommitGolfCandidate.GroupOpenVirtual

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open CommitGolfCandidate.Permutation.CounterSalt (coord input)
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

theorem before_keep (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) (k : Reg) (h : Clob k) :
    (beforeCall s i).getReg k=s.getReg k := (pre_spec s i ord left r).2.2.2.2.2 k h

def Saved (r : Reg) := r≠.x6 ∧ r≠.x7 ∧ r≠.x28 ∧ r≠.x30 ∧ r≠.x31 ∧ r≠.x14 ∧ r≠.x17

theorem finish_keep (s : MachineState) (i : Index) (ord left : Nat) (r : Input s i ord left) (y : BitVec 1600)
    (k : Reg) (h : Saved k) : (finishOne s i left y).getReg k=s.getReg k := by
  obtain ⟨h6,h7,h28,h30,h31,h14,h17⟩:=h
  simp only [finishOne,next_keeps _ _ _ h14 h17,copied_keeps _ _ h28,choose_keeps _ _ h31 h30,
    receives,writeBits_register,before_keep s i ord left r k ⟨h6,h7,h28,h30,h31⟩]

theorem finish_regs (s : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left ≤ 16777216)
    (r : Input s i ord left) (y : BitVec 1600) :
    Registers (finishOne s i left y) (ord+1) (left-1) ∧ (finishOne s i left y).pc=finalPC left ∧
      (finishOne s i left y).mem=(installed (receives s i y) i).mem := by
  obtain ⟨_,pc,idx,off,_,_⟩:=pre_spec s i ord left r
  have pr:=before_regs s i ord left r
  let w:=receives s i y
  let a:=choose w
  let b:=copied a
  have wr (k : Reg) : w.getReg k=(beforeCall s i).getReg k := writeBits_register ..
  have wp : w.pc=address 766 := by rw [show w.pc=(beforeCall s i).pc+4 from written_pc ..,pc];rfl
  obtain ⟨ap,ar,ad⟩:=chosen w i wp ((wr _).trans idx) ((wr _).trans off) ((wr _).trans pr.output) ((wr _).trans pr.salt)
  have keep (k : Reg) (h28 : k≠.x28 :=by decide) (h30 : k≠.x30 :=by decide) (h31 : k≠.x31 :=by decide) :
      b.getReg k=(beforeCall s i).getReg k :=
    (copied_keeps a k h28).trans ((choose_keeps w k h31 h30).trans (wr k))
  have post:=next_ok b ord left (copied_pc a ap) l hi ((keep .x14).trans pr.index) ((keep .x17).trans pr.leftReg)
  have saved (k : Reg) (safe : Saved k :=by unfold Saved;decide) := finish_keep s i ord left r y k safe
  refine ⟨⟨(saved .x10).trans r.input,(saved .x12).trans r.output,(saved .x5).trans r.selector,
    (saved .x11).trans r.width,(saved .x13).trans r.primitive,post.2.2.1,post.2.2.2.1,
    (saved .x22).trans r.salt,(saved .x26).trans r.base,(saved .x29).trans r.divReg⟩,post.2.1,?_⟩
  exact post.2.2.2.2.trans ((copied_mem a i ar ad).trans (by
    change (installed (choose w) i).mem=(installed w i).mem
    simp only [installed,MachineState.setMem,MachineState.getMem,chosen_memory w]))

def selectedWord (i : Index) (j : Fin 2) := (if (coord i).2.val=0 then 23 else 2*((coord i).2.val-1))+j.val

theorem reply_at (s : MachineState) (i : Index) (y : BitVec 1600) (j : Fin 2) :
    (receives s i y).getMem (readAt i+BitVec.ofNat 64 (8*j.val)) =
      PackedLeaves.Counter.slice (replyWords y) (coord i).2 j := by
  have rh := (coord i).2.isLt
  have jj:=j.isLt
  have sel : selectedWord i j<25 := by unfold selectedWord;split <;> omega
  have a : readAt i+BitVec.ofNat 64 (8*j.val)=wordAddress (192+selectedWord i j) := by
    unfold readAt wordAddress;rw [←BitVec.ofNat_add];unfold offAt Grouped.sliceByte selectedWord
    exact congrArg (BitVec.ofNat 64) (by split <;> omega)
  rw [a]
  have w:=permutation_write_memory (beforeCall s i) 192 (192+selectedWord i j) y (by decide) (by omega)
  change memoryView (writeBits (beforeCall s i) (wordAddress 192) y) (192+selectedWord i j)=_
  rw [w,writeWindow,dif_pos (by omega)]
  unfold PackedLeaves.Counter.slice
  apply congrArg (replyWords y)
  apply Fin.ext
  change 192+selectedWord i j-192=_
  unfold selectedWord;simp

theorem installs_salt (s : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left ≤ 16777216)
    (r : Input s i ord left) (y : BitVec 1600) (j : Fin 2) :
    (finishOne s i left y).getMem (destAt i+BitVec.ofNat 64 (8*j.val))=
      PackedLeaves.Counter.slice (replyWords y) (coord i).2 j := by
  have eq := (finish_regs s i ord left l hi r y).2.2
  rw [←reply_at s i y j]
  change (finishOne s i left y).mem _=_
  rw [eq];unfold installed
  fin_cases j <;> simp [MachineState.setMem,MachineState.getMem]

theorem outside_writes (s : MachineState) (i : Index) (ord left : Nat) (l : 0<left) (hi : left≤16777216)
    (r : Input s i ord left) (y : BitVec 1600) (w : Nat) (fit : w<2^33)
    (above : w≠128 ∧ (w<192 ∨ 217≤w))
    (apart : w≠872415748+2*i.val ∧ w≠872415748+2*i.val+1) :
    memoryView (finishOne s i left y) w=memoryView s w := by
  let f:=finishOne s i left y
  have fin := (finish_regs s i ord left l hi r y).2.2
  have init := (pre_spec s i ord left r).2.2.2.2.1
  have ix : i.val<16777216:=i.isLt
  have eq0 : destAt i=wordAddress (872415748+2*i.val) := by
    unfold destAt wordAddress;congr 1 <;> omega
  have eq1 : destAt i+8=wordAddress (872415748+2*i.val+1) := by rw [eq0,wordAddress_add (872415748+2*i.val) 1];rfl
  have distinct (v : Nat) (hv : v<2^33) (ne : w≠v) : wordAddress w≠wordAddress v :=
    fun h => ne (wordAddress_injective_of_bound (by omega) (by omega) h)
  have n0 : wordAddress w≠destAt i := eq0 ▸ distinct _ (by omega) apart.1
  have n1 : wordAddress w≠destAt i+8 := eq1 ▸ distinct _ (by omega) apart.2
  change (finishOne s i left y).mem (wordAddress w)=_
  rw [fin]
  change (installed (receives s i y) i).getMem (wordAddress w)=_
  rw [installed,MachineState.getMem_setMem_ne n1,MachineState.getMem_setMem_ne n0]
  change memoryView (writeBits (beforeCall s i) (wordAddress 192) y) w=_
  rw [permutation_write_memory _ _ _ _ (by decide) fit,writeWindow,dif_neg (by omega)]
  change (beforeCall s i).mem _=_
  rw [init]
  change (s.setMem 1024 (ctrAt i)).getMem (wordAddress w)=_
  exact MachineState.getMem_setMem_ne (distinct 128 (by decide) above.1)

end TwoPermutationPrototype.GroupedOpening
