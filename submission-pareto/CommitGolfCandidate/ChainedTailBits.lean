import CommitGolfCandidate.ChainedTailTraverseEntry

/-! Bit-list interpretation of native accumulator words and codec output bytes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def tailBitsWord (size : Nat) (bits : List Bool) : BitVec size :=
  BitVec.ofFnLE fun b => bits.getD b.val false

theorem tail_bits_word_bit (size : Nat) (bits : List Bool) (bit : Nat) (inside : bit<size) :
    (tailBitsWord size bits).getLsbD bit = bits.getD bit false := by
  rw [tailBitsWord,BitVec.getLsbD_ofFnLE,dite_eq_left inside]

theorem tail_bits_drop_getD (bits : List Bool) (offset bit : Nat) :
    (bits.drop offset).getD bit false = bits.getD (offset+bit) false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem tail_bits_word_setWidth (size width : Nat) (bits : List Bool) (bound : bits.length≤size) :
    (tailBitsWord size bits).setWidth width = tailBitsWord width bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [BitVec.getLsbD_setWidth,tail_bits_word_bit width bits bit inside]
  by_cases source : bit<size
  · rw [tail_bits_word_bit size bits bit source]
    simp [inside]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega),List.getD_eq_default bits false (by omega)]
    simp

theorem tail_bits_word_drop (size : Nat) (bits : List Bool) (offset : Nat) (bound : bits.length≤size) :
    tailBitsWord size bits >>> offset = tailBitsWord size (bits.drop offset) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [BitVec.getLsbD_ushiftRight,tail_bits_word_bit size _ bit inside,tail_bits_drop_getD]
  by_cases source : offset+bit<size
  · exact tail_bits_word_bit size bits (offset+bit) source
  · rw [BitVec.getLsbD_of_ge _ _ (by omega),List.getD_eq_default bits false (by omega)]

theorem tail_bits_word_append (front back : List Bool) :
    tailBitsWord 64 front ||| (tailBitsWord 64 back <<< front.length) = tailBitsWord 64 (front++back) := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [BitVec.getLsbD_or,tail_bits_word_bit 64 front bit inside,BitVec.getLsbD_shiftLeft,
    tail_bits_word_bit 64 back (bit-front.length) (by omega),
    tail_bits_word_bit 64 (front++back) bit inside]
  by_cases before : bit<front.length
  · rw [List.getD_append front back false bit before]
    simp [inside,before]
  · rw [List.getD_append_right front back false bit (by omega),
      List.getD_eq_default front false (by omega)]
    simp [inside,before]

theorem tail_bits_codec_byte (bits : List Bool) (byte : Nat) :
    (SplitCodec.packBits bits.length (fun bit => bits.getD bit false)).getD byte 0 =
      tailBitsWord 8 (bits.drop (8*byte)) := by
  by_cases inside : byte<(bits.length+7)/8
  · simp only [SplitCodec.packBits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
      inside,↓reduceDIte,Option.getD_some]
    apply BitVec.eq_of_getLsbD_eq
    intro bit small
    rw [BitVec.getLsbD_ofFnLE,dite_eq_left small,tail_bits_word_bit 8 _ bit small,tail_bits_drop_getD]
    by_cases present : 8*byte+bit<bits.length
    · simp [present]
    · rw [ite_eq_right present,List.getD_eq_default bits false (by omega)]
  · rw [List.getD_eq_default _ 0 (by simpa using Nat.le_of_not_gt inside)]
    apply BitVec.eq_of_getLsbD_eq
    intro bit small
    change (0#8).getLsbD bit = _
    rw [BitVec.getLsbD_zero,tail_bits_word_bit 8 _ bit small,tail_bits_drop_getD,
      List.getD_eq_default bits false (by omega)]

end CommitGolfCandidate.Chained.Native
