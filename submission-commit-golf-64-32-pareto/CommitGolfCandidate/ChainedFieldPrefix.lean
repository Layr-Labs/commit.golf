import CommitGolfCandidate.ChainedFieldHeader

/-! Extend completed low-body and descriptor prefixes by one initialized raw field. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

structure RawField where
  low : Proof
  high : List Bool
  padding : Proof
  highBound : high.length<7
  paddingBound : padding.length<3

def RawField.skip (field : RawField) : Fin 4 := ⟨1+field.padding.length,by have := field.paddingBound; omega⟩
def RawField.width (field : RawField) : Fin 7 := ⟨field.high.length,field.highBound⟩
def RawField.bytes (field : RawField) : Proof := field.low++tailBitsWord 8 field.high::field.padding
def RawField.state (field : RawField) (s : MachineState) : MachineState :=
  preparedFieldState field.skip field.width field.low.length s
def rawFieldsBytes (fields : List RawField) : Proof := fields.flatMap RawField.bytes
def rawFieldsLow (fields : List RawField) : Proof := fields.flatMap RawField.low
def rawFieldsMeta (fields : List RawField) : Proof := fields.flatMap fun field => descriptorBytes [field.high]

structure RawFieldsReady (fields : List RawField) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (source outputBase metaBase : Nat) : Prop where
  sourcePointer : s.getReg .x5=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 (outputBase+outputPrefix.length)
  metaPointer : s.getReg .x7=BitVec.ofNat 64 (metaBase+metaPrefix.length)
  input : BytesAt s (BitVec.ofNat 64 source) (rawFieldsBytes fields++suffix)
  output : BytesAt s (BitVec.ofNat 64 outputBase) outputPrefix
  metadata : BytesAt s (BitVec.ofNat 64 metaBase) metaPrefix
  ordered : outputBase+outputPrefix.length≤source
  separate : source+(rawFieldsBytes fields).length+suffix.length≤metaBase
  room : metaBase+metaPrefix.length+2*fields.length<2^64

theorem prepared_preserves_completed (skip : Fin 4) (width : Fin 7)
    (low bytes : Proof) (s : MachineState) (source destination scratch base : Nat)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source)
    (destinationReg : s.getReg .x6=BitVec.ofNat 64 destination)
    (scratchReg : s.getReg .x7=BitVec.ofNat 64 scratch)
    (body : BytesAt s (s.getReg .x5) low) (memory : BytesAt s (BitVec.ofNat 64 base) bytes)
    (ordered : destination≤source) (sourceEnd : source+low.length<2^64)
    (outputEnd : destination+low.length≤scratch) (scratchEnd : scratch+2<2^64)
    (completed : base+bytes.length≤scratch)
    (apart : base+bytes.length≤destination ∨ destination+low.length≤base) :
    BytesAt (preparedFieldState skip width low.length s) (BitVec.ofNat 64 base) bytes := by
  unfold preparedFieldState
  apply compact_field_preserves_completed low bytes (fieldHeaderPrefix skip width s 2)
    source destination scratch base
  · rw [field_header_frame skip width s .x5 (by decide) (by decide),sourceReg]
  · rw [field_header_frame skip width s .x6 (by decide) (by decide),destinationReg]
  · rw [field_header_frame skip width s .x7 (by decide) (by decide),scratchReg]
  · rw [field_header_frame skip width s .x5 (by decide) (by decide)]
    exact body
  · exact memory
  · exact ordered
  · exact sourceEnd
  · exact outputEnd
  · exact scratchEnd
  · exact completed
  · exact apart

theorem raw_fields_step (field : RawField) (fields : List RawField)
    (suffix outputPrefix metaPrefix : Proof) (s : MachineState) (source outputBase metaBase : Nat)
    (ready : RawFieldsReady (field::fields) suffix outputPrefix metaPrefix s source outputBase metaBase) :
    RawFieldsReady fields suffix (outputPrefix++field.low) (metaPrefix++descriptorBytes [field.high])
      (field.state s) (source+field.bytes.length) outputBase metaBase := by
  have rawLength : field.bytes.length=field.low.length+1+field.padding.length := by
    simp only [RawField.bytes,List.length_append,List.length_cons]
    omega
  have separate : source+field.low.length+1+field.padding.length+
      (rawFieldsBytes fields).length+suffix.length≤metaBase := by
    have bound := ready.separate
    change source+(field.bytes++rawFieldsBytes fields).length+suffix.length≤metaBase at bound
    rw [List.length_append,rawLength] at bound
    omega
  have room : metaBase+metaPrefix.length+2<2^64 := by
    have bound := ready.room
    simp only [List.length_cons] at bound
    omega
  have input : BytesAt s (BitVec.ofNat 64 source)
      (field.low++tailBitsWord 8 field.high::(field.padding++(rawFieldsBytes fields++suffix))) := by
    simpa only [rawFieldsBytes,List.flatMap_cons,RawField.bytes,List.append_assoc,List.cons_append] using ready.input
  have result := prepared_raw_field field.skip field.width field.low field.padding
    (rawFieldsBytes fields++suffix) field.high s source (outputBase+outputPrefix.length)
    (metaBase+metaPrefix.length) ready.sourcePointer ready.outputPointer ready.metaPointer rfl rfl input
    ready.ordered (by simp only [List.length_append]; omega) room
  have body : BytesAt s (s.getReg .x5) field.low := by
    rw [ready.sourcePointer]
    exact ((bytes_at_append s _ field.low _).mp input).1
  have outputEnd : outputBase+outputPrefix.length+field.low.length≤metaBase := by
    have ordered := ready.ordered
    omega
  have oldOutput := prepared_preserves_completed field.skip field.width field.low outputPrefix s
    source (outputBase+outputPrefix.length) (metaBase+metaPrefix.length) outputBase
    ready.sourcePointer ready.outputPointer ready.metaPointer body ready.output ready.ordered
    (by omega) (by omega) room (by omega) (Or.inl (by omega))
  have oldMeta := prepared_preserves_completed field.skip field.width field.low metaPrefix s
    source (outputBase+outputPrefix.length) (metaBase+metaPrefix.length) metaBase
    ready.sourcePointer ready.outputPointer ready.metaPointer body ready.metadata ready.ordered
    (by omega) (by omega) room (by omega) (Or.inr outputEnd)
  have nextSource : source+field.bytes.length=source+field.low.length+1+field.padding.length := by
    rw [rawLength]
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [nextSource]
    exact result.2.2.2.1
  · simpa only [RawField.state,List.length_append,Nat.add_assoc] using result.2.2.2.2.1
  · have next := result.2.2.2.2.2
    simpa only [RawField.state,descriptor_bytes_length,List.length_singleton,List.length_append,Nat.mul_one,Nat.add_assoc] using next
  · rw [nextSource]
    exact result.2.2.1
  · apply (bytes_at_append _ _ outputPrefix field.low).mpr
    refine ⟨oldOutput,?_⟩
    rw [←BitVec.ofNat_add]
    exact result.1
  · apply (bytes_at_append _ _ metaPrefix (descriptorBytes [field.high])).mpr
    refine ⟨oldMeta,?_⟩
    rw [←BitVec.ofNat_add]
    exact result.2.1
  · simp only [List.length_append]
    have ordered := ready.ordered
    rw [nextSource]
    omega
  · rw [nextSource]
    exact separate
  · have bound := ready.room
    simp only [List.length_append,descriptor_bytes_length,List.length_cons,List.length_nil] at bound ⊢
    omega

end CommitGolfCandidate.Chained.Native
