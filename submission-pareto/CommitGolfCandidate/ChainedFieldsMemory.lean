import CommitGolfCandidate.ChainedFieldPrefix

/-! Whole-list low-body and descriptor construction from a raw packet memory view. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

@[irreducible] def rawFieldsState : List RawField → MachineState → MachineState
  | [],s => s
  | field::fields,s => rawFieldsState fields (field.state s)

theorem raw_fields_zero (s : MachineState) : rawFieldsState [] s=s := by unfold rawFieldsState; rfl
theorem raw_fields_cons (field : RawField) (fields : List RawField) (s : MachineState) :
    rawFieldsState (field::fields) s=rawFieldsState fields (field.state s) := by
  conv => lhs; unfold rawFieldsState

theorem raw_fields_memory (fields : List RawField) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (source outputBase metaBase : Nat)
    (ready : RawFieldsReady fields suffix outputPrefix metaPrefix s source outputBase metaBase) :
    RawFieldsReady [] suffix (outputPrefix++rawFieldsLow fields) (metaPrefix++rawFieldsMeta fields)
      (rawFieldsState fields s) (source+(rawFieldsBytes fields).length) outputBase metaBase := by
  induction fields generalizing s source outputPrefix metaPrefix with
  | nil => simpa only [raw_fields_zero,rawFieldsBytes,rawFieldsLow,rawFieldsMeta,List.flatMap_nil,
      List.append_nil,List.length_nil,Nat.add_zero] using ready
  | cons field fields ih =>
    have next := raw_fields_step field fields suffix outputPrefix metaPrefix s source outputBase metaBase ready
    have result := ih (outputPrefix++field.low) (metaPrefix++descriptorBytes [field.high])
      (field.state s) (source+field.bytes.length) next
    simpa only [raw_fields_cons,rawFieldsBytes,rawFieldsLow,rawFieldsMeta,List.flatMap_cons,
      List.length_append,List.append_assoc,Nat.add_assoc] using result

theorem raw_fields_meta_rows (fields : List RawField) :
    rawFieldsMeta fields=descriptorBytes (fields.map RawField.high) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    simpa only [rawFieldsMeta,List.flatMap_cons,List.map_cons,descriptorBytes,List.cons_append,List.nil_append] using
      congrArg (fun tail => tailBitsWord 8 field.high::BitVec.ofNat 8 field.high.length::tail) ih

theorem raw_fields_low_room (fields : List RawField) :
    (rawFieldsLow fields).length+fields.length≤(rawFieldsBytes fields).length := by
  induction fields with
  | nil => simp [rawFieldsLow,rawFieldsBytes]
  | cons field fields ih =>
    change (field.low++rawFieldsLow fields).length+(field::fields).length≤
      (field.bytes++rawFieldsBytes fields).length
    simp only [RawField.bytes,List.length_append,List.length_cons]
    omega

theorem raw_fields_construct_memory (fields : List RawField) (suffix : Proof)
    (s : MachineState) (source outputBase metaBase : Nat)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metaBase)
    (input : BytesAt s (BitVec.ofNat 64 source) (rawFieldsBytes fields++suffix))
    (ordered : outputBase≤source)
    (separate : source+(rawFieldsBytes fields).length+suffix.length≤metaBase)
    (room : metaBase+2*fields.length<2^64) :
    BytesAt (rawFieldsState fields s) (BitVec.ofNat 64 outputBase) (rawFieldsLow fields) ∧
    BytesAt (rawFieldsState fields s) (BitVec.ofNat 64 metaBase) (descriptorBytes (fields.map RawField.high)) ∧
    BytesAt (rawFieldsState fields s) (BitVec.ofNat 64 (source+(rawFieldsBytes fields).length)) suffix := by
  have ready : RawFieldsReady fields suffix [] [] s source outputBase metaBase := by
    refine ⟨sourcePointer,?_,?_,input,?_,?_,?_,separate,?_⟩
    · simpa using outputPointer
    · simpa using metaPointer
    · intro index inside; simp at inside
    · intro index inside; simp at inside
    · simpa using ordered
    · simpa using room
  have result := raw_fields_memory fields suffix [] [] s source outputBase metaBase ready
  have low := result.output
  have metadataView := result.metadata
  have rest := result.input
  simp only [List.nil_append] at low metadataView
  rw [raw_fields_meta_rows] at metadataView
  exact ⟨low,metadataView,rest⟩

end CommitGolfCandidate.Chained.Native
