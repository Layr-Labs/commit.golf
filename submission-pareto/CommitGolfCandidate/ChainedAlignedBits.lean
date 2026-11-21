import CommitGolfCandidate.ChainedTailBits

/-! Byte-aligned concatenation for the native interior-tail byte layout. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

def packedBits (bits : List Bool) : Proof :=
  SplitCodec.packBits bits.length (fun bit => bits.getD bit false)

@[simp] theorem packed_bits_length (bits : List Bool) : (packedBits bits).length=(bits.length+7)/8 := by
  exact SplitCodec.pack_bits_length _ _

theorem packed_bits_byte (bits : List Bool) (index : Nat) :
    (packedBits bits).getD index 0=tailBitsWord 8 (bits.drop (8*index)) :=
  tail_bits_codec_byte bits index

theorem packed_bits_append (front back : List Bool) (aligned : front.length%8=0) :
    packedBits (front++back)=packedBits front++packedBits back := by
  have size : (front.length+7)/8=front.length/8 := by omega
  have bytes : (packedBits front).length=front.length/8 := by rw [packed_bits_length,size]
  apply List.ext_getElem
  · simp only [packed_bits_length,List.length_append]
    omega
  intro index left right
  have data : (packedBits (front++back)).getD index 0 =
      (packedBits front++packedBits back).getD index 0 := by
    by_cases before : index<front.length/8
    · rw [List.getD_append _ _ 0 index (by omega),packed_bits_byte,packed_bits_byte]
      apply BitVec.eq_of_getLsbD_eq
      intro bit inside
      rw [tail_bits_word_bit 8 _ bit inside,tail_bits_word_bit 8 _ bit inside,
        tail_bits_drop_getD,tail_bits_drop_getD]
      exact List.getD_append front back false (8*index+bit) (by omega)
    · rw [List.getD_append_right _ _ 0 index (by omega),packed_bits_byte,packed_bits_byte,bytes]
      apply BitVec.eq_of_getLsbD_eq
      intro bit inside
      rw [tail_bits_word_bit 8 _ bit inside,tail_bits_word_bit 8 _ bit inside,
        tail_bits_drop_getD,tail_bits_drop_getD,List.getD_append_right front back false (8*index+bit) (by omega)]
      congr 1
      omega
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem left,
    List.getElem?_eq_getElem right,Option.getD_some] using data

end CommitGolfCandidate.Chained.Native
