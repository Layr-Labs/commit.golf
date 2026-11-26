import CommitGolfCandidate.ReconstructedCommitInput
import CommitGolfCandidate.ReconstructedCommitWindows
import CommitGolfCandidate.WriteMemory
import RiscvZkvm.Rv64.Logic.ByteOps

namespace CommitGolfCandidate.Reconstruction.CommitWrite
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)

theorem word_read (s : MachineState) (w : Nat) : readBuffer s (8*w) 8 = memoryView s w := by
  have sliced := read_buffer_slice s (8*w) 32 0 8 (by decide)
  have word := read_digest_word s (8*w) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,memoryView,wordAddress] using sliced.symm.trans word

/-- An aligned wide syscall write has exactly the word-level effect used by the
salt generator, including both of its overlapping output windows. -/
theorem words (s : MachineState) (n dst w : Nat) (value : BitVec (64*n))
    (room : dst+n ≤ 2^33) (readable : w < 2^33) :
    memoryView (writeBits s (wordAddress dst) value) w =
      writeWindow (memoryView s) dst (splitBlocks 64 n value) w := by
  rw [← word_read,writeWindow]
  split <;> rename_i h
  · change readBuffer _ (8*w) 8 = value.extractLsb' (64*(w-dst)) 64
    rw [show 64*(w-dst) = 8*(8*(w-dst)) by omega]
    apply read_serialized_slice
    intro j hj
    have b := write_bits_byte s (wordAddress dst) value (8*(w-dst)+j) (by omega) (by omega)
    simpa only [wordAddress,← BitVec.ofNat_add,
      show 8*dst+(8*(w-dst)+j) = 8*w+j by omega] using b
  · rw [← word_read]
    exact write_bits_read_outside s value (8*dst) (8*w) 8 (by omega) (by omega) (by omega)

private theorem offset (w j : Nat) (small : j < 8) :
    byteOffset (BitVec.ofNat 64 (8*w+j)) = j := by
  unfold byteOffset
  rw [BitVec.toNat_and,BitVec.toNat_ofNat]
  change ((8*w+j)%2^64) &&& (2^3-1) = j
  rw [Nat.and_two_pow_sub_one_eq_mod]; omega

private theorem align (w j : Nat) (small : j < 8) :
    alignToDword (BitVec.ofNat 64 (8*w+j)) = wordAddress w := by
  have div := alignToDword_add_byteOffset (BitVec.ofNat 64 (8*w+j))
  rw [offset w j small,BitVec.ofNat_add] at div
  have cancel := congrArg (fun a : Word => a - BitVec.ofNat 64 j) div
  simpa only [BitVec.add_sub_cancel,wordAddress,BitVec.ofNat_add] using cancel

theorem clear_salt_byte (s : MachineState) (dst w : Nat) (h : dst < 2^61) (hw : w < 2^61) :
    memoryView (s.setByte (BitVec.ofNat 64 (8*dst+7)) 0) w =
      writeWord (memoryView s) dst ((memoryView s dst) &&& 0x00ffffffffffffff) w := by
  unfold MachineState.setByte
  rw [align dst 7 (by decide),offset dst 7 (by decide),memory_at_store h hw]
  congr 2
  change replaceByte (s.getMem (wordAddress dst)) 7 0 = s.getMem (wordAddress dst) &&& 0x00ffffffffffffff
  simp [replaceByte]

/-- After keeping the first 240 reply bits, SH sets the high halfword to the leaf tag. -/
theorem mark_leaf (s : MachineState) (dst w : Nat) (h : dst < 2^61) (hw : w < 2^61) :
    memoryView (s.setHalfword (BitVec.ofNat 64 (8*dst+6)) 65535) w =
      writeWord (memoryView s) dst ((memoryView s dst) ||| 0xffff000000000000) w := by
  unfold MachineState.setHalfword
  rw [align dst 6 (by decide),offset dst 6 (by decide),memory_at_store h hw]
  congr 2
  change replaceHalfword (s.getMem (wordAddress dst)) 3 65535 =
    s.getMem (wordAddress dst) ||| 0xffff000000000000
  generalize s.getMem (wordAddress dst) = v
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  interval_cases k <;> simp [replaceHalfword]

end CommitGolfCandidate.Reconstruction.CommitWrite
