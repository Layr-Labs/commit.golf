import CommitGolfCandidate.ChainedInverseBitStream

/-! The inverse stream reconstructs the generic codec's typed payload values. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

theorem split_word_congr (low high : Nat) (front₀ front₁ tail₀ tail₁ : List Bool)
    (front : ∀ bit, bit<low → front₀.getD bit false=front₁.getD bit false)
    (back : ∀ bit, bit<high → tail₀.getD bit false=tail₁.getD bit false) :
    word low high front₀ tail₀=word low high front₁ tail₁ := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [word,BitVec.getLsbD_ofFnLE,dite_eq_left inside]
  by_cases before : bit<low
  · rw [ite_eq_left before,ite_eq_left before,front bit before]
  · rw [ite_eq_right before,ite_eq_right before,back (bit-low) (by omega)]

theorem split_fields_congr (spec : Spec) (front₀ front₁ tail₀ tail₁ : List Bool)
    (front : ∀ bit, bit<lowCount spec → front₀.getD bit false=front₁.getD bit false)
    (back : ∀ bit, bit<highCount spec → tail₀.getD bit false=tail₁.getD bit false) :
    fields spec front₀ tail₀=fields spec front₁ tail₁ := by
  induction spec generalizing front₀ front₁ tail₀ tail₁ with
  | nil => rfl
  | cons field spec ih =>
    obtain ⟨low,high⟩ := field
    simp only [fields]
    congr 1
    · apply split_word_congr
      · intro bit inside
        apply front bit
        change bit<low+lowCount spec
        omega
      · intro bit inside
        apply back bit
        change bit<high+highCount spec
        omega
    · apply ih
      · intro bit inside
        rw [tail_bits_drop_getD,tail_bits_drop_getD]
        apply front (low+bit)
        change low+bit<low+lowCount spec
        omega
      · intro bit inside
        rw [tail_bits_drop_getD,tail_bits_drop_getD]
        apply back (high+bit)
        change high+bit<high+highCount spec
        omega

theorem codec_bits_getD (count : Nat) (proof : Proof) (bit : Nat) (inside : bit<count) :
    (unpackBits count proof).getD bit false=readBit proof bit := by
  simp only [unpackBits,List.getD_eq_getElem?_getD,List.getElem?_ofFn,inside,↓reduceDIte,Option.getD_some]

theorem read_bit_drop (proof : Proof) (bytes bit : Nat) :
    readBit (proof.drop bytes) bit=readBit proof (8*bytes+bit) := by
  simp only [readBit,List.getD_eq_getElem?_getD,List.getElem?_drop]
  rw [show (8*bytes+bit)/8=bytes+bit/8 by omega,show (8*bytes+bit)%8=bit%8 by omega]

theorem inverse_plan_payload (spec : Spec) (front : List Bool) (proof : Proof)
    (small : ∀ field ∈ spec, field.2≤6) :
    let plan := tailParsePlan (spec.map Prod.snd) [] (fun i => byteBits (proof.getD i 0))
    fieldsFromRows spec front plan.fields=fields spec front (unpackBits (highCount spec) proof) := by
  have widths : ∀ width ∈ spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have consumed := inverse_plan_read_exact (spec.map Prod.snd) (fun i => byteBits (proof.getD i 0))
    (fun i => byte_bits_length _) widths
  have fit : highCount spec≤8*(tailParsePlan (spec.map Prod.snd) [] (fun i => byteBits (proof.getD i 0))).read := by
    change (spec.map Prod.snd).sum≤_
    rw [consumed]
    omega
  have result := inverse_plan_fields spec front (fun i => byteBits (proof.getD i 0))
    (fun i => byte_bits_length _) small
  dsimp only at result ⊢
  rw [pull_proof_bits] at result
  refine result.trans (split_fields_congr spec front front _ _ (by intros; rfl) ?_)
  intro bit inside
  rw [codec_bits_getD _ proof bit (by omega),codec_bits_getD _ proof bit inside]

theorem split_decode_parts (spec : Spec) (proof : Proof) (aligned : lowCount spec%8=0) :
    fields spec (unpackBits (lowCount spec) proof)
      (unpackBits (highCount spec) (proof.drop (lowCount spec/8)))=decode spec proof := by
  unfold decode
  apply split_fields_congr
  · intro bit inside
    have taken : ((unpackBits (lowCount spec+highCount spec) proof).take (lowCount spec)).getD bit false=
        (unpackBits (lowCount spec+highCount spec) proof).getD bit false := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_take,inside,↓reduceIte]
    rw [taken,codec_bits_getD _ proof bit inside,codec_bits_getD _ proof bit (by omega)]
  · intro bit inside
    rw [tail_bits_drop_getD,codec_bits_getD _ _ bit inside,
      codec_bits_getD _ proof (lowCount spec+bit) (by omega),read_bit_drop]
    rw [show 8*(lowCount spec/8)+bit=lowCount spec+bit by omega]

theorem inverse_payload_decode (spec : Spec) (proof : Proof)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6) :
    let tail := proof.drop (lowCount spec/8)
    let plan := tailParsePlan (spec.map Prod.snd) [] (fun i => byteBits (tail.getD i 0))
    fieldsFromRows spec (unpackBits (lowCount spec) proof) plan.fields=decode spec proof := by
  exact (inverse_plan_payload spec _ _ small).trans (split_decode_parts spec proof (low_count_aligned spec aligned))

end CommitGolfCandidate.Chained.Native
