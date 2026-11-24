import CommitGolfCandidate.ChainedParsedMetadata
import CommitGolfCandidate.ChainedInverseCanonical

/-! Bind the native acceptance register and scratch bytes to the strict payload decoder. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

theorem parsed_payload_descriptor (spec : Spec) (proof : Proof) (input : Nat → List Bool)
    (s : MachineState) (buffer : TailParseBuffer s []) (byteSize : ∀ i, (input i).length=8)
    (small : ∀ field ∈ spec, field.2≤6)
    (table : ParseWidthsAt s (s.getReg .x21) (spec.map Prod.snd))
    (memory : ParseInputAt s (s.getReg .x20) input spec.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) ((spec.map Prod.snd).map fun _ => []))
    (fit : 2*spec.length<2^64) :
    let plan := tailParsePlan (spec.map Prod.snd) [] input
    let payload := fieldsFromRows spec (unpackBits (lowCount spec) proof) plan.fields
    let after := tailValidatePrefix (tailParsedFieldsState spec.length s) 3
    BytesAt after (s.getReg .x21) (descriptorBytes (highRows payload)) := by
  have widths : ∀ width ∈ spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have shape := tail_parse_plan_widths (spec.map Prod.snd) [] input byteSize widths
  have count : (tailParsePlan (spec.map Prod.snd) [] input).fields.length=spec.length := by
    simpa only [List.length_map] using congrArg List.length shape
  have model := native_tail_parse_plan (spec.map Prod.snd) [] input s buffer byteSize widths table
    (by simpa only [List.length_map] using memory) apart (by simpa only [List.length_map] using fit)
  dsimp only
  rw [high_rows_from_rows spec _ _ shape]
  apply parsed_rows_descriptor_at s _ _ _ (by rwa [shape]) (by rwa [count])
  intro query
  have same : (tailValidatePrefix (tailParsedFieldsState spec.length s) 3).getByte query=
      (tailParsedFieldsState spec.length s).getByte query := by
    simp only [MachineState.getByte,tail_validate_memory]
  exact same.trans (by simpa only [List.length_map] using model.2.1 query)

theorem parsed_payload_accepts (spec : Spec) (proof : Proof) (input : Nat → List Bool)
    (s : MachineState) (buffer : TailParseBuffer s []) (byteSize : ∀ i, (input i).length=8)
    (aligned : ∀ field ∈ spec, field.1%8=0) (small : ∀ field ∈ spec, field.2≤6)
    (enough : lowCount spec/8≤proof.length)
    (table : ParseWidthsAt s (s.getReg .x21) (spec.map Prod.snd))
    (memory : ParseInputAt s (s.getReg .x20) input spec.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) ((spec.map Prod.snd).map fun _ => []))
    (fit : 2*spec.length<2^64) (endFit : (proof.drop (lowCount spec/8)).length<2^64)
    (endPointer : s.getReg .x19=s.getReg .x20+BitVec.ofNat 64 (proof.drop (lowCount spec/8)).length)
    (source : ∀ index, index<(proof.drop (lowCount spec/8)).length →
      input index=byteBits ((proof.drop (lowCount spec/8)).getD index 0)) :
    let plan := tailParsePlan (spec.map Prod.snd) [] input
    let payload := fieldsFromRows spec (unpackBits (lowCount spec) proof) plan.fields
    let after := tailValidatePrefix (tailParsedFieldsState spec.length s) 3
    after.getReg .x24=1#64 → unpack spec proof=some payload ∧ decode spec proof=payload := by
  have widths : ∀ width ∈ spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have model := native_tail_parse_result (spec.map Prod.snd) [] input s buffer byteSize widths table
    (by simpa only [List.length_map] using memory) apart (by simpa only [List.length_map] using fit)
    (proof.drop (lowCount spec/8)).length endFit endPointer
  dsimp only at model ⊢
  simp only [List.length_map] at model
  intro accepted
  have valid : (tailParsePlan (spec.map Prod.snd) [] input).read=(proof.drop (lowCount spec/8)).length ∧
      ∀ index, index<(tailParsePlan (spec.map Prod.snd) [] input).carry.length →
        (tailParsePlan (spec.map Prod.snd) [] input).carry.getD index false=false := by
    by_contra invalid
    have zero := model.1
    rw [ite_eq_right invalid] at zero
    have impossible : (1#64)=(0#64) := accepted.symm.trans zero
    exact (by decide : ¬(1#64)=(0#64)) impossible
  exact inverse_strict_accepts spec proof input aligned small enough byteSize source valid.1 valid.2

theorem packed_bits_padding (bits : List Bool) (index : Nat) (outside : bits.length ≤ index) :
    readBit (packedBits bits) index=false := by
  unfold readBit
  rw [packed_bits_byte,tail_bits_word_bit 8 _ (index%8) (Nat.mod_lt _ (by decide)),tail_bits_drop_getD,
    show 8*(index/8)+index%8=index by omega]
  exact List.getD_eq_default bits false outside

theorem inverse_plan_packed_complete (widths : List Nat) (bits : List Bool) (input : Nat → List Bool)
    (count : bits.length=widths.sum) (byteSize : ∀ index, (input index).length=8)
    (small : ∀ width∈widths, width≤6)
    (source : ∀ index, index<(packedBits bits).length → input index=byteBits ((packedBits bits).getD index 0)) :
    (tailParsePlan widths [] input).read=(packedBits bits).length ∧
      ∀ index, index<(tailParsePlan widths [] input).carry.length →
        (tailParsePlan widths [] input).carry.getD index false=false := by
  have read : (tailParsePlan widths [] input).read=(packedBits bits).length := by
    rw [inverse_plan_read_exact widths input byteSize small,packed_bits_length,count]
  refine ⟨read,?_⟩
  have shape := tail_parse_plan_widths widths [] input byteSize small
  have rowLength : (tailParsePlan widths [] input).fields.flatten.length=bits.length := by
    rw [List.length_flatten,shape,count]
  have full := tail_parse_plan_bits widths [] input
  rw [List.nil_append,read,pull_bit_bytes_congr input _ _ source,pull_proof_bits] at full
  have total := congrArg List.length full
  simp only [List.length_append,unpackBits,List.length_ofFn,rowLength] at total
  intro index inside
  have bounded : bits.length+index<8*(packedBits bits).length := by omega
  have observed := congrArg (fun stream : List Bool => stream.getD (bits.length+index) false) full
  rw [List.getD_append_right _ _ false _ (by omega),rowLength,Nat.add_sub_cancel_left,
    codec_bits_getD _ _ _ bounded] at observed
  exact observed.trans (packed_bits_padding bits _ (by omega))

theorem encoded_tail_plan_complete (spec : Spec) (payload : Payload spec) (input : Nat → List Bool)
    (aligned : ∀ field∈spec, field.1%8=0) (small : ∀ field∈spec, field.2≤6)
    (byteSize : ∀ index, (input index).length=8)
    (source : ∀ index, index<((encode payload).drop (lowCount spec/8)).length →
      input index=byteBits (((encode payload).drop (lowCount spec/8)).getD index 0)) :
    (tailParsePlan (spec.map Prod.snd) [] input).read=((encode payload).drop (lowCount spec/8)).length ∧
      ∀ index, index<(tailParsePlan (spec.map Prod.snd) [] input).carry.length →
        (tailParsePlan (spec.map Prod.snd) [] input).carry.getD index false=false := by
  have tail : (encode payload).drop (lowCount spec/8)=packedBits (highs payload) := by
    rw [encode_descriptors payload aligned,←low_bytes_length payload aligned,List.drop_left,high_rows_flatten]
  rw [tail] at source ⊢
  apply inverse_plan_packed_complete
  · exact highs_length payload
  · exact byteSize
  · intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  · exact source

theorem parsed_payload_complete (spec : Spec) (payload : Payload spec) (input : Nat → List Bool)
    (s : MachineState) (buffer : TailParseBuffer s []) (byteSize : ∀ index, (input index).length=8)
    (aligned : ∀ field∈spec, field.1%8=0) (small : ∀ field∈spec, field.2≤6)
    (table : ParseWidthsAt s (s.getReg .x21) (spec.map Prod.snd))
    (memory : ParseInputAt s (s.getReg .x20) input spec.length)
    (apart : TailApart (s.getReg .x21) (s.getReg .x20) ((spec.map Prod.snd).map fun _ => []))
    (fit : 2*spec.length<2^64) (endFit : ((encode payload).drop (lowCount spec/8)).length<2^64)
    (endPointer : s.getReg .x19=s.getReg .x20+BitVec.ofNat 64 ((encode payload).drop (lowCount spec/8)).length)
    (source : ∀ index, index<((encode payload).drop (lowCount spec/8)).length →
      input index=byteBits (((encode payload).drop (lowCount spec/8)).getD index 0)) :
    (tailValidatePrefix (tailParsedFieldsState spec.length s) 3).getReg .x24=1#64 := by
  have widths : ∀ width∈spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have model := native_tail_parse_result (spec.map Prod.snd) [] input s buffer byteSize widths table
    (by simpa only [List.length_map] using memory) apart (by simpa only [List.length_map] using fit)
    ((encode payload).drop (lowCount spec/8)).length endFit endPointer
  have good := encoded_tail_plan_complete spec payload input aligned small byteSize source
  simpa only [List.length_map,ite_eq_left good] using model.1

end CommitGolfCandidate.Chained.Native
