import CommitGolfCandidate.Stage3cMachineTag
import CommitGolfCandidate.Stage3cMaskMemory
import CommitGolfCandidate.Stage3cLeafMemory
import CommitGolfCandidate.Stage3cPlainBlock
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 12000

theorem parentBlock_first (d : Height) (l r : Output) (chain : 8≤d.val ∧ d.val<16) :
    parentBlock l r (tagWord d 0)=pack (.inl (workClass d,r ++ l)) := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_value,symbolCode,workClass,if_pos chain]
  unfold parentBlock
  rw [append_value,append_value,tagMatchesFirst d (by omega)]
  simp

theorem parentBlock_next (d : Height) (j : Fin 15) (v : Output) :
    parentBlock v 0 (tagWord d ⟨j.val+1,by omega⟩)=encodeNext d (j.val+1) v := by
  rw [encodeNext_valid d (j.val+1) v (by omega) (by have :=j.isLt;omega)]
  apply BitVec.eq_of_toNat_eq;rw [pack_value];simp only [symbolCode]
  unfold parentBlock;rw [append_value,append_value,append_value,tagMatchesNext];simp

theorem read_word (s : MachineState) (a : Nat) (aligned : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  have slice:=read_buffer_slice s a 32 0 8 (by decide)
  have word:=read_digest_word s a 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using slice.symm.trans word

theorem read_parent_block (s : MachineState) (a : Nat) (l r : Output) (tag : Word)
    (left : readBuffer s a 32=l) (right : readBuffer s (a+32) 32=r)
    (t : readBuffer s (a+64) 8=tag) (pad : readBuffer s (a+72) 24=0) :
    readBuffer s a 96=parentBlock l r tag := by
  have lo:=read_join s a 32 32
  have high:=read_join s (a+64) 8 24
  have all:=read_join s a 64 32
  rw [show a+64+8=a+72 by omega,pad,t] at high
  rw [left,right] at lo
  change _=(readBuffer s a 64).extractLsb' 0 512 at lo
  change _=(readBuffer s (a+64) 32).extractLsb' 0 256 at high
  change _=(readBuffer s a 96).extractLsb' 0 768 at all
  simp only [BitVec.extractLsb'_eq_self] at lo high all
  rw [←lo,←high] at all;exact all.symm

theorem read_after_store_outside (s : MachineState) (a : Nat) (v : Word) (b n : Nat)
    (aligned : a%8=0) (aFit : a+8≤2^64) (bFit : b+n≤2^64) (apart : b+n≤a ∨ a+8≤b) :
    readBuffer (s.setMem (BitVec.ofNat 64 a) v) b n=readBuffer s b n := by
  unfold readBuffer;congr 1
  apply Finset.sum_congr rfl;intro j hj
  have inRange:=Finset.mem_range.mp hj
  have wordNe : alignToDword (BitVec.ofNat 64 (b+j))≠BitVec.ofNat 64 a := by
    intro eq
    have pieces:=split_address (BitVec.ofNat 64 (b+j))
    rw [eq,byte_offset,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b+j<2^64),←BitVec.ofNat_add] at pieces
    have num:=congrArg BitVec.toNat pieces
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+(b+j)%8<2^64),Nat.mod_eq_of_lt (by omega : b+j<2^64)] at num
    omega
  simp only [MachineState.getByte,MachineState.getMem_setMem_ne wordNe]
end CommitGolfCandidate.Chained.BinaryMachine
