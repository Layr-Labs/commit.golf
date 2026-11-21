import CommitGolfCandidate.ChainedInverseFieldFrame
import CommitGolfCandidate.ChainedFieldsMemory

/-! Physical source/output/scratch geometry for whole-payload reconstruction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def RawPaddingAt (s : MachineState) : Word → List RawField → Prop
  | _,[] => True
  | base,field::fields =>
    BytesAt s (base+BitVec.ofNat 64 (field.low.length+1)) field.padding ∧
      RawPaddingAt s (base+BitVec.ofNat 64 field.bytes.length) fields

theorem raw_padding_frame (s after : MachineState) (base : Word) (fields : List RawField)
    (padding : RawPaddingAt s base fields)
    (same : ∀ index, index<(rawFieldsBytes fields).length →
      after.getByte (base+BitVec.ofNat 64 index)=s.getByte (base+BitVec.ofNat 64 index)) :
    RawPaddingAt after base fields := by
  induction fields generalizing base with
  | nil => trivial
  | cons field fields ih =>
    have total : (rawFieldsBytes (field::fields)).length=field.low.length+1+field.padding.length+
        (rawFieldsBytes fields).length := by simp [rawFieldsBytes,RawField.bytes]; omega
    constructor
    · intro index inside
      rw [byte_offset_add,same _ (by rw [total]; omega),←byte_offset_add]
      exact padding.1 index inside
    · apply ih _ padding.2
      intro index inside
      have bound : field.bytes.length+index<(rawFieldsBytes (field::fields)).length := by
        change field.bytes.length+index<(field.bytes++rawFieldsBytes fields).length
        rw [List.length_append]
        omega
      rw [byte_offset_add,same _ bound]

structure InverseFieldsReady (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat) : Prop where
  sourcePointer : s.getReg .x5=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 (outputBase+completed.length)
  metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata
  input : BytesAt s (BitVec.ofNat 64 source) (rawFieldsLow fields++suffix)
  output : BytesAt s (BitVec.ofNat 64 outputBase) completed
  table : BytesAt s (BitVec.ofNat 64 metadata) (rawFieldsMeta fields)
  padding : RawPaddingAt s (BitVec.ofNat 64 (outputBase+completed.length)) fields
  inputBefore : source+(rawFieldsLow fields).length+suffix.length<outputBase
  outputBefore : outputBase+completed.length+(rawFieldsBytes fields).length≤metadata
  room : metadata+2*fields.length<2^64

theorem inverse_fields_step (field : RawField) (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady (field::fields) suffix completed s source outputBase metadata) :
    InverseFieldsReady fields suffix (completed++field.bytes) (field.inverseState s)
      (source+field.low.length) outputBase (metadata+2) := by
  have rawLength : field.bytes.length=field.low.length+1+field.padding.length := by
    simp only [RawField.bytes,List.length_append,List.length_cons]
    omega
  have inputBefore : source+field.low.length+(rawFieldsLow fields).length+suffix.length<outputBase := by
    have bound := ready.inputBefore
    change source+(field.low++rawFieldsLow fields).length+suffix.length<outputBase at bound
    rw [List.length_append] at bound
    omega
  have outputBefore : outputBase+completed.length+field.bytes.length+(rawFieldsBytes fields).length≤metadata := by
    have bound := ready.outputBefore
    change outputBase+completed.length+(field.bytes++rawFieldsBytes fields).length≤metadata at bound
    rw [List.length_append] at bound
    omega
  have room : metadata+2+2*fields.length<2^64 := by
    have bound := ready.room
    simp only [List.length_cons] at bound
    omega
  have input : BytesAt s (BitVec.ofNat 64 source) (field.low++(rawFieldsLow fields++suffix)) := by
    simpa only [rawFieldsLow,List.flatMap_cons,List.append_assoc] using ready.input
  have body : BytesAt s (s.getReg .x5) field.low := by
    rw [ready.sourcePointer]
    exact ((bytes_at_append s _ _ _).mp input).1
  have ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) field.low.length := by
    rw [ready.sourcePointer,ready.outputPointer]
    intro index inside written before
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have apart : ∀ index, index<field.low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index := by
    intro index inside
    rw [ready.metaPointer,ready.outputPointer,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  have value : s.getByte (s.getReg .x7)=tailBitsWord 8 field.high := by
    rw [ready.metaPointer]
    have data := ready.table 0 (by change 0<(descriptorBytes [field.high]++rawFieldsMeta fields).length; simp)
    simpa only [rawFieldsMeta,List.flatMap_cons,descriptorBytes,List.cons_append,List.nil_append,
      BitVec.add_zero,List.getD_cons_zero] using data
  have preserve (base : Nat) (bytes : Proof) (memory : BytesAt s (BitVec.ofNat 64 base) bytes)
      (position : base+bytes.length≤outputBase+completed.length ∨ outputBase+completed.length+field.low.length+1≤base)
      (bound : base+bytes.length<2^64) : BytesAt (field.inverseState s) (BitVec.ofNat 64 base) bytes := by
    apply inverse_raw_field_preserves field bytes s _ body ahead value apart memory
    intro index inside written before
    rw [ready.outputPointer,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by omega)
    rcases position with left | right <;> omega
  have output := preserve outputBase completed ready.output (Or.inl (by omega)) (by omega)
  have current := inverse_raw_field_bytes field s body ahead value apart
    (by rw [ready.outputPointer]; exact ready.padding.1) (by omega)
  rw [ready.outputPointer] at current
  have unread : BytesAt s (BitVec.ofNat 64 (source+field.low.length)) (rawFieldsLow fields++suffix) := by
    have view := ((bytes_at_append s _ _ _).mp input).2
    simpa only [←BitVec.ofNat_add] using view
  have nextInput := preserve (source+field.low.length) (rawFieldsLow fields++suffix) unread
    (Or.inl (by simp only [List.length_append]; omega)) (by simp only [List.length_append]; omega)
  have tableSize : (rawFieldsMeta (field::fields)).length=2*(field::fields).length := by
    rw [raw_fields_meta_rows,descriptor_bytes_length,List.length_map]
  have table := preserve metadata (rawFieldsMeta (field::fields)) ready.table
    (Or.inr (by omega)) (by rw [tableSize]; exact ready.room)
  change BytesAt (field.inverseState s) (BitVec.ofNat 64 metadata)
    (descriptorBytes [field.high]++rawFieldsMeta fields) at table
  have nextTable := ((bytes_at_append _ _ _ _).mp table).2
  have nextPadding := raw_padding_frame s (field.inverseState s) _ fields ready.padding.2 (by
    intro index inside
    rw [inverse_raw_field_plan field s body ahead value apart,write_byte_list_preserves]
    intro written before
    rw [ready.outputPointer,←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by simp only [List.length_append,List.length_singleton] at before; omega)
    simp only [List.length_append,List.length_singleton] at before
    omega)
  refine ⟨?_,?_,?_,nextInput,?_,?_,?_,inputBefore,?_,room⟩
  · rw [inverse_raw_field_source,ready.sourcePointer,←BitVec.ofNat_add]
  · rw [inverse_raw_field_destination,ready.outputPointer,←BitVec.ofNat_add,List.length_append]
    congr 1
    omega
  · rw [inverse_raw_field_descriptor,ready.metaPointer]
    change BitVec.ofNat 64 metadata+BitVec.ofNat 64 2=_
    rw [←BitVec.ofNat_add]
  · apply (bytes_at_append _ _ completed field.bytes).mpr
    refine ⟨output,?_⟩
    simpa only [←BitVec.ofNat_add] using current
  · simpa only [descriptor_bytes_length,List.length_singleton,Nat.mul_one,←BitVec.ofNat_add] using nextTable
  · simpa only [List.length_append,←BitVec.ofNat_add,Nat.add_assoc] using nextPadding
  · simp only [List.length_append]
    omega

end CommitGolfCandidate.Chained.Native
