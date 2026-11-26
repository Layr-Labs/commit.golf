import CommitGolfCandidate.ChainedInversePrefix

/-! The native length/padding flag implies acceptance by the strict payload codec. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

theorem packed_zero_carry (bits carry : List Bool) (proof : Proof)
    (size : (packedBits bits).length=proof.length)
    (full : bits++carry=unpackBits (8*proof.length) proof)
    (zero : ∀ index, index<carry.length → carry.getD index false=false) :
    packedBits bits=proof := by
  have total := congrArg List.length full
  simp only [List.length_append,unpackBits,List.length_ofFn] at total
  apply List.ext_getElem
  · exact size
  · intro index left right
    have same : (packedBits bits).getD index 0=proof.getD index 0 := by
      rw [packed_bits_byte]
      apply BitVec.eq_of_getLsbD_eq
      intro bit inside
      rw [tail_bits_word_bit 8 _ bit inside,tail_bits_drop_getD]
      have observed := congrArg (fun stream : List Bool => stream.getD (8*index+bit) false) full
      rw [codec_bits_getD _ proof _ (by omega)] at observed
      unfold readBit at observed
      rw [show (8*index+bit)/8=index by omega,show (8*index+bit)%8=bit by omega] at observed
      by_cases before : 8*index+bit<bits.length
      · rw [List.getD_append _ _ false _ before] at observed
        exact observed
      · rw [List.getD_append_right _ _ false _ (by omega),zero _ (by omega)] at observed
        rw [List.getD_eq_default bits false (by omega)]
        exact observed
    simpa only [List.getD_eq_getElem _ _ left,List.getD_eq_getElem _ _ right] using same

theorem low_bytes_from_rows (spec : Spec) (proof : Proof) (rows : List (List Bool))
    (widths : rows.map List.length=spec.map Prod.snd)
    (aligned : ∀ field ∈ spec, field.1%8=0) (enough : lowCount spec/8≤proof.length) :
    lowBytes (fieldsFromRows spec (unpackBits (lowCount spec) proof) rows)=proof.take (lowCount spec/8) := by
  rw [fields_from_rows spec _ rows [] widths,low_bytes_packed _ aligned,lows_fields_prefix]
  · rw [List.take_of_length_le (by simp [unpackBits])]
    have divisible := low_count_aligned spec aligned
    conv_lhs => rw [show lowCount spec=8*(lowCount spec/8) by omega]
    exact packed_codec_bytes proof _ enough
  · simp [unpackBits]

theorem inverse_canonical (spec : Spec) (proof : Proof) (input : Nat → List Bool)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (enough : lowCount spec/8≤proof.length) (byteSize : ∀ i, (input i).length=8)
    (source : ∀ index, index<(proof.drop (lowCount spec/8)).length →
      input index=byteBits ((proof.drop (lowCount spec/8)).getD index 0))
    (length : (tailParsePlan (spec.map Prod.snd) [] input).read=(proof.drop (lowCount spec/8)).length)
    (padding : ∀ index, index<(tailParsePlan (spec.map Prod.snd) [] input).carry.length →
      (tailParsePlan (spec.map Prod.snd) [] input).carry.getD index false=false) :
    let plan := tailParsePlan (spec.map Prod.snd) [] input
    let payload := fieldsFromRows spec (unpackBits (lowCount spec) proof) plan.fields
    encode payload=proof := by
  have widths : ∀ width ∈ spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have shape := tail_parse_plan_widths (spec.map Prod.snd) [] input byteSize widths
  have bits := tail_parse_plan_bits (spec.map Prod.snd) [] input
  rw [List.nil_append,length,pull_bit_bytes_congr input _ _ source,pull_proof_bits] at bits
  have rowSize : (tailParsePlan (spec.map Prod.snd) [] input).fields.flatten.length=(spec.map Prod.snd).sum := by
    rw [List.length_flatten,shape]
  have read := inverse_plan_read_exact (spec.map Prod.snd) input byteSize widths
  have size : (packedBits (tailParsePlan (spec.map Prod.snd) [] input).fields.flatten).length=
      (proof.drop (lowCount spec/8)).length := by
    rw [packed_bits_length,rowSize,←read,length]
  have tail := packed_zero_carry _ _ _ size bits padding
  dsimp only
  rw [encode_descriptors _ aligned,low_bytes_from_rows spec proof _ shape aligned enough,
    high_rows_from_rows spec _ _ shape,tail,List.take_append_drop]

theorem inverse_strict_accepts (spec : Spec) (proof : Proof) (input : Nat → List Bool)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (enough : lowCount spec/8≤proof.length) (byteSize : ∀ i, (input i).length=8)
    (source : ∀ index, index<(proof.drop (lowCount spec/8)).length →
      input index=byteBits ((proof.drop (lowCount spec/8)).getD index 0))
    (length : (tailParsePlan (spec.map Prod.snd) [] input).read=(proof.drop (lowCount spec/8)).length)
    (padding : ∀ index, index<(tailParsePlan (spec.map Prod.snd) [] input).carry.length →
      (tailParsePlan (spec.map Prod.snd) [] input).carry.getD index false=false) :
    let payload := fieldsFromRows spec (unpackBits (lowCount spec) proof)
      (tailParsePlan (spec.map Prod.snd) [] input).fields
    unpack spec proof=some payload ∧ decode spec proof=payload := by
  have canonical := inverse_canonical spec proof input aligned small enough byteSize source length padding
  dsimp only at canonical ⊢
  constructor
  · conv_lhs => rw [←canonical,unpack_encode]
  · conv_lhs => rw [←canonical,decode_encode]

end CommitGolfCandidate.Chained.Native
