import CommitGolfCandidate.ChainedInverseDecode

/-! Recover the untouched low-byte body and the parsed high rows of a decoded payload. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

theorem bits_prefix_of_getD (count : Nat) (bits : List Bool) (value : Fin count → Bool)
    (enough : count≤bits.length) (same : ∀ bit, value bit=bits.getD bit.val false) :
    List.ofFn value=bits.take count := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_take]
    omega
  · intro bit left right
    have inside : bit<count := by simpa only [List.length_ofFn] using left
    have result := same ⟨bit,inside⟩
    simp only [List.getElem_ofFn,List.getElem_take]
    simpa only [List.getD_eq_getElem _ _ (show bit<bits.length by omega)] using result

theorem split_word_low_bits (low high : Nat) (front tail : List Bool) (enough : low≤front.length) :
    (List.ofFn fun bit : Fin low => (word low high front tail).getLsbD bit.val)=front.take low := by
  apply bits_prefix_of_getD low front _ enough
  intro bit
  simp only [word,BitVec.getLsbD_ofFnLE,dite_eq_left (show bit.val<low+high by have := bit.isLt; omega),
    ite_eq_left bit.isLt]

theorem split_word_high_bits (low high : Nat) (front tail : List Bool) (enough : high≤tail.length) :
    (List.ofFn fun bit : Fin high => (word low high front tail).getLsbD (low+bit.val))=tail.take high := by
  apply bits_prefix_of_getD high tail _ enough
  intro bit
  simp only [word,BitVec.getLsbD_ofFnLE,dite_eq_left (show low+bit.val<low+high by have := bit.isLt; omega),
    ite_eq_right (show ¬low+bit.val<low by omega),Nat.add_sub_cancel_left]

theorem lows_fields_prefix (spec : Spec) (front tail : List Bool) (enough : lowCount spec≤front.length) :
    lows (fields spec front tail)=front.take (lowCount spec) := by
  induction spec generalizing front tail with
  | nil => simp [lows,fields,lowCount]
  | cons field spec ih =>
    obtain ⟨low,high⟩ := field
    have bound : low+lowCount spec≤front.length := enough
    rw [fields,lows,split_word_low_bits low high front tail (by omega),ih]
    · change front.take low++(front.drop low).take (lowCount spec)=front.take (low+lowCount spec)
      exact List.take_add.symm
    · simp only [List.length_drop]
      omega

theorem codec_bits_take (count total : Nat) (proof : Proof) (enough : count≤total) :
    (unpackBits total proof).take count=unpackBits count proof := by
  apply List.ext_getElem
  · simp only [unpackBits,List.length_ofFn,List.length_take]
    omega
  · intro bit left right
    simp only [unpackBits,List.getElem_take,List.getElem_ofFn]

theorem lows_decode (spec : Spec) (proof : Proof) :
    lows (decode spec proof)=unpackBits (lowCount spec) proof := by
  rw [decode,lows_fields_prefix]
  · rw [List.take_take,Nat.min_self,codec_bits_take _ _ proof (by omega)]
  · simp only [List.length_take,unpackBits,List.length_ofFn]
    omega

theorem packed_codec_bytes (proof : Proof) (count : Nat) (enough : count≤proof.length) :
    packedBits (unpackBits (8*count) proof)=proof.take count := by
  apply List.ext_getElem
  · simp only [packed_bits_length,unpackBits,List.length_ofFn,List.length_take]
    omega
  · intro index left right
    have inside : index<count := by simpa only [List.length_take,Nat.min_eq_left enough] using right
    have byte := packed_bits_byte (unpackBits (8*count) proof) index
    have same : (packedBits (unpackBits (8*count) proof)).getD index 0=proof.getD index 0 := by
      rw [byte]
      apply BitVec.eq_of_getLsbD_eq
      intro bit small
      rw [tail_bits_word_bit 8 _ bit small,tail_bits_drop_getD,codec_bits_getD _ proof _ (by omega)]
      unfold readBit
      rw [show (8*index+bit)/8=index by omega,show (8*index+bit)%8=bit by omega]
    simp only [List.getElem_take]
    simpa only [List.getD_eq_getElem _ _ left,List.getD_eq_getElem _ _ (show index<proof.length by omega)] using same

theorem low_bytes_decode (spec : Spec) (proof : Proof)
    (aligned : ∀ field ∈ spec, field.1%8=0) (enough : lowCount spec/8≤proof.length) :
    lowBytes (decode spec proof)=proof.take (lowCount spec/8) := by
  rw [low_bytes_packed _ aligned,lows_decode]
  have divisible := low_count_aligned spec aligned
  conv_lhs => rw [show lowCount spec=8*(lowCount spec/8) by omega]
  exact packed_codec_bytes proof _ enough

theorem high_rows_from_rows (spec : Spec) (front : List Bool) (rows : List (List Bool))
    (widths : rows.map List.length=spec.map Prod.snd) :
    highRows (fieldsFromRows spec front rows)=rows := by
  induction spec generalizing front rows with
  | nil => cases rows <;> simp_all [fieldsFromRows,highRows]
  | cons field spec ih =>
    obtain ⟨low,high⟩ := field
    cases rows with
    | nil => simp at widths
    | cons row rows =>
      have parts : row.length=high ∧ rows.map List.length=spec.map Prod.snd := by simpa using widths
      simp only [fieldsFromRows,List.headD_cons,List.tail_cons,highRows]
      rw [split_word_high_bits low high front row (by omega),List.take_of_length_le (by omega),ih _ rows parts.2]

end CommitGolfCandidate.Chained.Native
