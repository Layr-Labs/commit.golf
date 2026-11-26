import CommitGolfCandidate.ChainedFieldsExecution

/-! Typed codec payloads supply the raw fields consumed by native construction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

private theorem padding_head_bound (pads : List Proof) (small : ∀ pad ∈ pads, pad.length≤2) :
    (pads.headD []).length<3 := by
  cases pads with
  | nil => simp
  | cons pad pads =>
    have bound := small pad (by simp)
    simpa using (show pad.length<3 by omega)

private theorem padding_tail_bound (pads : List Proof) (small : ∀ pad ∈ pads, pad.length≤2) :
    ∀ pad ∈ pads.tail, pad.length≤2 := by
  intro pad member
  cases pads with
  | nil => simp at member
  | cons head tail => exact small pad (by simp_all)

def payloadRawFields : {spec : Spec} → (payload : Payload spec) → (pads : List Proof) →
    (small : ∀ field ∈ spec, field.2≤6) → (padSmall : ∀ pad ∈ pads, pad.length≤2) → List RawField
  | [],.nil,_,_,_ => []
  | (low,high)::spec,.cons value rest,pads,small,padSmall =>
    { low := packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val)
      high := List.ofFn fun bit : Fin high => value.getLsbD (low+bit.val)
      padding := pads.headD []
      highBound := by
        simp only [List.length_ofFn]
        have bound := small (low,high) (by simp)
        omega
      paddingBound := padding_head_bound pads padSmall }::
    payloadRawFields rest pads.tail (fun field member => small field (by simp [member]))
      (padding_tail_bound pads padSmall)

private theorem low_fields_cons (field : RawField) (fields : List RawField) :
    rawFieldsLow (field::fields)=field.low++rawFieldsLow fields := rfl

private theorem low_payload_cons (low high : Nat) (spec : Spec) (value : BitVec (low+high))
    (rest : Payload spec) : lowBytes (.cons value rest)=
      packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val)++lowBytes rest := rfl

theorem payload_raw_fields_low {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    rawFieldsLow (payloadRawFields payload pads small padSmall)=lowBytes payload := by
  induction payload generalizing pads with
  | nil => rfl
  | @cons low high spec value rest ih =>
    simp only [payloadRawFields,low_fields_cons,low_payload_cons]
    rw [ih]

theorem payload_raw_fields_high {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    (payloadRawFields payload pads small padSmall).map RawField.high=highRows payload := by
  induction payload generalizing pads with
  | nil => rfl
  | @cons low high spec value rest ih =>
    simp only [payloadRawFields,List.map_cons,highRows]
    rw [ih]

theorem payload_raw_fields_count {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    (payloadRawFields payload pads small padSmall).length=spec.length := by
  have lengths := congrArg List.length (payload_raw_fields_high payload pads small padSmall)
  simpa only [List.length_map,high_rows_length] using lengths

theorem payload_raw_fields_steps {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    rawFieldsSteps (payloadRawFields payload pads small padSmall)=4*(lowBytes payload).length+7*spec.length := by
  rw [raw_fields_steps,payload_raw_fields_low,payload_raw_fields_count]

theorem payload_raw_fields_length {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    (rawFieldsBytes (payloadRawFields payload pads small padSmall)).length=
      (lowBytes payload).length+spec.length+(pads.take spec.length).flatten.length := by
  induction payload generalizing pads with
  | nil => simp [payloadRawFields,rawFieldsBytes,lowBytes,lowRows]
  | @cons low high spec value rest ih =>
    change ((packedBits (List.ofFn fun bit : Fin low => value.getLsbD bit.val)++
      tailBitsWord 8 (List.ofFn fun bit : Fin high => value.getLsbD (low+bit.val))::pads.headD [])++
      rawFieldsBytes (payloadRawFields rest pads.tail _ _)).length=_
    rw [List.length_append,ih,low_payload_cons]
    cases pads with
    | nil => simp only [List.headD_nil,List.tail_nil,List.take_nil,List.flatten_nil,List.length_nil,
        List.length_append,List.length_cons]; omega
    | cons pad pads =>
      simp only [List.headD_cons,List.tail_cons,List.length_append,List.length_cons,List.take_succ_cons,List.flatten_cons]
      omega

theorem native_construct_payload_fields {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2)
    (suffix : Proof) (s : MachineState) (source outputBase metaBase : Nat)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metaBase)
    (input : BytesAt s (BitVec.ofNat 64 source)
      (rawFieldsBytes (payloadRawFields payload pads small padSmall)++suffix))
    (ordered : outputBase≤source)
    (separate : source+(rawFieldsBytes (payloadRawFields payload pads small padSmall)).length+suffix.length≤metaBase)
    (room : metaBase+2*spec.length<2^64) :
    BytesAt (rawFieldsState (payloadRawFields payload pads small padSmall) s)
      (BitVec.ofNat 64 outputBase) (lowBytes payload) ∧
    BytesAt (rawFieldsState (payloadRawFields payload pads small padSmall) s)
      (BitVec.ofNat 64 metaBase) (descriptorBytes (highRows payload)) := by
  have result := raw_fields_construct_memory (payloadRawFields payload pads small padSmall) suffix s
    source outputBase metaBase sourcePointer outputPointer metaPointer input ordered separate
    (by simpa only [payload_raw_fields_count] using room)
  constructor
  · simpa only [payload_raw_fields_low] using result.1
  · simpa only [payload_raw_fields_high] using result.2.1

end CommitGolfCandidate.Chained.Native
