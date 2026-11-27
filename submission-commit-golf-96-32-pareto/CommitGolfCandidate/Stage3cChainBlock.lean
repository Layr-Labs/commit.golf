import CommitGolfCandidate.Stage3cPointerEffect
import CommitGolfCandidate.Stage3cMachineTag
import CommitGolfCandidate.Stage3cMaskMemory
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 12000

def srcAddr (h : Height) (p : Nat) := nodeAddress h.val (2*p)
def dstAddr (h : Height) (p : Nat) := nodeAddress (h.val+1) p

theorem buffers {h : Height} {p : Nat} (hp : p<count h) :
    srcAddr h p+96≤MEMORY_BYTES ∧ srcAddr h p%8=0 ∧ dstAddr h p+32≤MEMORY_BYTES ∧ dstAddr h p%8=0 := by
  have above:=gap_ceiling h p hp
  have target:=parent_below_salts _ _ hp
  refine ⟨?_,aligned_node ..,?_,aligned_node ..⟩
  · change nodeAddress h.val (2*p)+96≤2^36
    unfold tagAddr tdBase levelOffset LENGTH LOG_LENGTH at above;omega
  · change nodeAddress (h.val+1) p+32≤2^36
    unfold rowBase at target;omega

def stageInput (H : Compression) (h : Height) (l r : Output) (j : Nat) :=
  (parentQueries H h l r j).getLastD 0

theorem read_congr_mem (s t : MachineState) (r n : Nat) (eq : s.mem=t.mem) :
    readBuffer s r n=readBuffer t r n := read_only_mem s t r n eq

theorem read_word (s : MachineState) (a : Nat) (aligned : a%8=0) :
    readBuffer s a 8=s.getMem (BitVec.ofNat 64 a) := by
  have slice:=read_buffer_slice s a 32 0 8 (by decide)
  have word:=read_digest_word s a 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero] using slice.symm.trans word

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
end CommitGolfCandidate.Chained.BinaryMachine
