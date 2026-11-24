import CommitGolfCandidate.ChainedOpeningEntry
import CommitGolfCandidate.ChainedSerialization

/-! Canonical cached words give exactly the raw bytes consumed by native fields. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem cached_low_byte (low high : Nat) (value : BitVec (low+high)) (index : Nat)
    (aligned : low%8=0) (inside : index<low/8) :
    (packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val)).getD index 0=
      value.extractLsb' (8*index) 8 := by
  rw [packed_bits_byte]
  apply BitVec.eq_of_getLsbD_eq
  intro bit small
  rw [tail_bits_word_bit _ _ bit small,tail_bits_drop_getD]
  have present : 8*index+bit<low := by omega
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,present,↓reduceDIte,Option.getD_some,
    BitVec.getLsbD_extractLsb',small,decide_true,Bool.true_and]

theorem cached_high_byte (low high : Nat) (value : BitVec (low+high)) :
    tailBitsWord 8 (List.ofFn fun bit : Fin high => value.getLsbD (low+bit.val))=
      value.extractLsb' low 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit small
  rw [tail_bits_word_bit _ _ bit small,BitVec.getLsbD_extractLsb']
  simp only [small,decide_true,Bool.true_and]
  by_cases inside : bit<high
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]
  · rw [List.getD_eq_default _ false (by simpa using Nat.le_of_not_gt inside),
      BitVec.getLsbD_of_ge _ _ (by omega)]

def cachedRawField (low high : Nat) (value : BitVec (low+high)) (padding : Nat)
    (highSmall : high<7) (paddingSmall : padding<3) : RawField :=
  ⟨packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val),
    List.ofFn (fun bit : Fin high => value.getLsbD (low+bit.val)),List.replicate padding 0,
    by simpa only [List.length_ofFn] using highSmall,
    by simpa only [List.length_replicate] using paddingSmall⟩

theorem cached_raw_field_byte (low high : Nat) (value : BitVec (low+high)) (padding index : Nat)
    (highSmall : high<7) (paddingSmall : padding<3) (aligned : low%8=0)
    (inside : index<low/8+1+padding) :
    ((cachedRawField low high value padding highSmall paddingSmall).bytes).getD index 0=
      value.extractLsb' (8*index) 8 := by
  have length : (packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val)).length=low/8 := by
    rw [packed_bits_length,List.length_ofFn]
    omega
  unfold RawField.bytes cachedRawField
  dsimp only
  by_cases before : index<low/8
  · rw [List.getD_append _ _ 0 index (by omega)]
    exact cached_low_byte low high value index aligned before
  · rw [List.getD_append_right _ _ 0 index (by omega)]
    by_cases last : index=low/8
    · subst index
      rw [length,Nat.sub_self,List.getD_cons_zero,cached_high_byte]
      congr 1
      omega
    · have offset : index-low/8>0 := by omega
      rw [length,show index-low/8=index-low/8-1+1 by omega,List.getD_cons_succ]
      have zero : (List.replicate padding (0 : BitVec 8)).getD (index-low/8-1) 0=0 := by simp
      rw [zero]
      apply BitVec.eq_of_getLsbD_eq
      intro bit small
      change (0#8).getLsbD bit=(value.extractLsb' (8*index) 8).getLsbD bit
      rw [BitVec.getLsbD_zero,BitVec.getLsbD_extractLsb',BitVec.getLsbD_of_ge _ _ (by omega)]
      simp

theorem cached_field_bytes_at (low high : Nat) (value : BitVec (low+high)) (padding : Nat)
    (highSmall : high<7) (paddingSmall : padding<3) (aligned : low%8=0)
    (s : MachineState) (address : Nat)
    (read : readBuffer s address (low/8+1+padding)=value.setWidth (8*(low/8+1+padding))) :
    BytesAt s (BitVec.ofNat 64 address) (cachedRawField low high value padding highSmall paddingSmall).bytes := by
  intro index inside
  have length : (cachedRawField low high value padding highSmall paddingSmall).bytes.length=low/8+1+padding := by
    simp only [cachedRawField,RawField.bytes,List.length_append,packed_bits_length,List.length_ofFn,
      List.length_cons,List.length_replicate]
    omega
  rw [length] at inside
  rw [cached_raw_field_byte low high value padding index highSmall paddingSmall aligned inside]
  have byte := read_buffer_byte s address (low/8+1+padding) index inside
  rw [read] at byte
  rw [←BitVec.ofNat_add]
  exact byte.symm.trans (by
    apply BitVec.eq_of_getLsbD_eq
    intro bit small
    simp only [BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,small,decide_true,Bool.true_and]
    simp only [show 8*index+bit<8*(low/8+1+padding) by omega,decide_true,Bool.true_and])

end CommitGolfCandidate.Chained.Native
