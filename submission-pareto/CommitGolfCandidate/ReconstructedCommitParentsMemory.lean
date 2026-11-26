import CommitGolfCandidate.ReconstructedCommitParentsCall
import CommitGolfCandidate.ReconstructedCommitParentsProjection
import RiscvZkvm.Rv64.Logic.ByteOps

namespace CommitGolfCandidate.Reconstruction.CommitParents
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding
set_option maxRecDepth 8192

def atWord (s : MachineState) (a : Nat) := s.getMem (BitVec.ofNat 64 a)

theorem cell_words (s : MachineState) (a : Nat) (align : a%8=0) :
    cell s a = ((atWord s (a+16) ++ atWord s (a+8)) ++ atWord s a,atWord s (a+24)) := by
  have split (x y z t : BitVec 64) : unpack (((x++y)++z)++t) = ((y++z)++t,x) := by
    have reass : ((x++y)++z)++t=x++((y++z)++t) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_append]
      split_ifs <;> first | rfl | omega | congr 1 <;> omega
    rw [reass]
    exact unpack_pack ((y++z)++t,x)
  unfold cell
  rw [read_digest_words s a align,split];rfl

private theorem address_ne {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro eq; apply h
  simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using congrArg BitVec.toNat eq

def putTop (s : MachineState) (dst : Nat) (hi : Word) := s.setMem (BitVec.ofNat 64 (dst+24)) hi

theorem putTop_cell (s : MachineState) (dst : Nat) (hi : Word) (align : dst%8=0) (limit : dst+32 ≤ 2^64) :
    cell (putTop s dst hi) dst = ((cell s dst).1,hi) := by
  rw [cell_words _ dst align,cell_words s dst align]
  unfold putTop atWord
  simp only [MachineState.getMem_setMem_eq,
    MachineState.getMem_setMem_ne (address_ne (by omega : dst+16<2^64) (by omega : dst+24<2^64) (by omega)),
    MachineState.getMem_setMem_ne (address_ne (by omega : dst+8<2^64) (by omega : dst+24<2^64) (by omega)),
    MachineState.getMem_setMem_ne (address_ne (by omega : dst<2^64) (by omega : dst+24<2^64) (by omega))]

private theorem byte_from_word (s : MachineState) (a : Nat) :
    s.getByte (BitVec.ofNat 64 a) = extractByte (atWord s (8*(a/8))) (a%8) := by
  have h := aligned_byte s (a/8) (a%8) (by omega)
  simpa only [show 8*(a/8)+a%8 = a by omega,Nat.div_eq_of_lt (show a%8<8 by omega),Nat.mul_zero,Nat.add_zero,
    Nat.mod_mod,atWord] using h

theorem putTop_frame (s : MachineState) (dst : Nat) (hi : Word) (align : dst%8=0) (limit : dst+32 ≤ 2^64) :
    Frame dst s (putTop s dst hi) := by
  intro a len bound separate
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro j hj
  have small := Finset.mem_range.1 hj
  have eq : atWord (putTop s dst hi) (8*((a+j)/8)) = atWord s (8*((a+j)/8)) :=
    MachineState.getMem_setMem_ne (address_ne (by omega) (by omega) (by omega))
  rw [byte_from_word,byte_from_word s,eq]

private theorem offset (a j : Nat) (aligned : a%8=0) (small : j<8) :
    byteOffset (BitVec.ofNat 64 (a+j)) = j := by
  unfold byteOffset
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  change ((a+j)%2^64) &&& (2^3-1) = j
  rw [Nat.and_two_pow_sub_one_eq_mod];omega

private theorem aligned_offset (a j : Nat) (align : a%8=0) (small : j<8) :
    alignToDword (BitVec.ofNat 64 (a+j)) = BitVec.ofNat 64 a := by
  have parts := alignToDword_add_byteOffset (BitVec.ofNat 64 (a+j))
  rw [offset a j align small,BitVec.ofNat_add] at parts
  have eq := congrArg (fun w : Word => w-BitVec.ofNat 64 j) parts
  simpa only [BitVec.add_sub_cancel,BitVec.ofNat_add] using eq

theorem half_store (s : MachineState) (dst : Nat) (v : BitVec 16) (align : dst%8=0) :
    s.setHalfword (BitVec.ofNat 64 (dst+30)) v = putTop s dst (replaceHalfword (atWord s (dst+24)) 3 v) := by
  unfold MachineState.setHalfword putTop atWord
  rw [show dst+30 = (dst+24)+6 by omega,aligned_offset (dst+24) 6 (by omega) (by decide),
    offset (dst+24) 6 (by omega) (by decide)]

theorem top_half_load (s : MachineState) (dst : Nat) (align : dst%8=0) :
    s.getHalfword (BitVec.ofNat 64 (dst+28)) = extractHalfword (atWord s (dst+24)) 2 := by
  unfold MachineState.getHalfword atWord
  rw [show dst+28=(dst+24)+4 by omega,aligned_offset (dst+24) 4 (by omega) (by decide),
    offset (dst+24) 4 (by omega) (by decide)]

theorem word_store (s : MachineState) (dst : Nat) (v : BitVec 32) (align : dst%8=0) :
    s.setWord32 (BitVec.ofNat 64 (dst+28)) v = putTop s dst (replaceWord32 (atWord s (dst+24)) 1 v) := by
  unfold MachineState.setWord32 putTop atWord
  rw [show dst+28=(dst+24)+4 by omega,aligned_offset (dst+24) 4 (by omega) (by decide),
    offset (dst+24) 4 (by omega) (by decide)]

end CommitGolfCandidate.Reconstruction.CommitParents
