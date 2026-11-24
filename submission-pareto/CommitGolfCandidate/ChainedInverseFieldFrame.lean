import CommitGolfCandidate.ChainedInverseField
import CommitGolfCandidate.ChainedFieldPrefix

/-! Trusted inverse-field setup and projected memory/register frames. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def RawField.inverseState (field : RawField) (s : MachineState) : MachineState :=
  inverseFieldState field.low.length (fieldHeaderPrefix field.skip field.width s 2)

theorem inverse_raw_field_plan (field : RawField) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) field.low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) field.low.length)
    (value : s.getByte (s.getReg .x7)=tailBitsWord 8 field.high)
    (apart : ∀ index, index<field.low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index)
    (query : Word) :
    (field.inverseState s).getByte query=
      writeByteList s.getByte (s.getReg .x6) (field.low++[tailBitsWord 8 field.high]) query := by
  have source := field_header_frame field.skip field.width s .x5 (by decide) (by decide)
  have destination := field_header_frame field.skip field.width s .x6 (by decide) (by decide)
  have scratch := field_header_frame field.skip field.width s .x7 (by decide) (by decide)
  have body' : BytesAt (fieldHeaderPrefix field.skip field.width s 2)
      ((fieldHeaderPrefix field.skip field.width s 2).getReg .x5) field.low := by
    rw [source]
    exact body
  have ahead' : CopyAhead ((fieldHeaderPrefix field.skip field.width s 2).getReg .x5)
      ((fieldHeaderPrefix field.skip field.width s 2).getReg .x6) field.low.length := by
    rwa [source,destination]
  have value' : (fieldHeaderPrefix field.skip field.width s 2).getByte
      ((fieldHeaderPrefix field.skip field.width s 2).getReg .x7)=tailBitsWord 8 field.high := by
    rwa [field_header_byte,scratch]
  have apart' : ∀ index, index<field.low.length →
      (fieldHeaderPrefix field.skip field.width s 2).getReg .x7≠
        (fieldHeaderPrefix field.skip field.width s 2).getReg .x6+BitVec.ofNat 64 index := by
    rwa [scratch,destination]
  exact native_inverse_field_plan field.low _ _ body' ahead' value' apart' query

theorem inverse_raw_field_preserves (field : RawField) (bytes : Proof) (s : MachineState) (base : Word)
    (body : BytesAt s (s.getReg .x5) field.low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) field.low.length)
    (value : s.getByte (s.getReg .x7)=tailBitsWord 8 field.high)
    (apart : ∀ index, index<field.low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index)
    (memory : BytesAt s base bytes)
    (separate : ∀ index, index<bytes.length → ∀ written, written<field.low.length+1 →
      base+BitVec.ofNat 64 index≠s.getReg .x6+BitVec.ofNat 64 written) :
    BytesAt (field.inverseState s) base bytes := by
  intro index inside
  rw [inverse_raw_field_plan field s body ahead value apart,write_byte_list_preserves]
  · exact memory index inside
  · intro written before
    exact separate index inside written (by simpa using before)

theorem inverse_raw_field_bytes (field : RawField) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) field.low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) field.low.length)
    (value : s.getByte (s.getReg .x7)=tailBitsWord 8 field.high)
    (apart : ∀ index, index<field.low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index)
    (pad : BytesAt s (s.getReg .x6+BitVec.ofNat 64 (field.low.length+1)) field.padding)
    (fit : field.bytes.length<2^64) :
    BytesAt (field.inverseState s) (s.getReg .x6) field.bytes := by
  let state := fieldHeaderPrefix field.skip field.width s 2
  have source : state.getReg .x5=s.getReg .x5 := field_header_frame _ _ _ .x5 (by decide) (by decide)
  have destination : state.getReg .x6=s.getReg .x6 := field_header_frame _ _ _ .x6 (by decide) (by decide)
  have scratch : state.getReg .x7=s.getReg .x7 := field_header_frame _ _ _ .x7 (by decide) (by decide)
  have body' : BytesAt state (state.getReg .x5) field.low := by rw [source]; exact body
  have ahead' : CopyAhead (state.getReg .x5) (state.getReg .x6) field.low.length := by rwa [source,destination]
  have value' : state.getByte (state.getReg .x7)=tailBitsWord 8 field.high := by rw [scratch]; exact value
  have apart' : ∀ index, index<field.low.length → state.getReg .x7≠state.getReg .x6+BitVec.ofNat 64 index := by
    rwa [scratch,destination]
  have pad' : BytesAt state (state.getReg .x6+BitVec.ofNat 64 (field.low.length+1)) field.padding := by
    rw [destination]
    exact pad
  have bound : field.low.length+1+field.padding.length<2^64 := by
    simp only [RawField.bytes,List.length_append,List.length_cons] at fit
    omega
  have result := native_inverse_field_bytes field.low field.padding (tailBitsWord 8 field.high) state
    body' ahead' value' apart' pad' bound
  rw [destination] at result
  simpa only [RawField.inverseState,RawField.bytes,List.append_assoc,List.singleton_append] using result

theorem inverse_raw_field_source (field : RawField) (s : MachineState) :
    (field.inverseState s).getReg .x5=s.getReg .x5+BitVec.ofNat 64 field.low.length := by
  rw [RawField.inverseState,inverse_field_source,field_header_frame _ _ _ .x5 (by decide) (by decide)]

theorem inverse_raw_field_destination (field : RawField) (s : MachineState) :
    (field.inverseState s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 field.bytes.length := by
  rw [RawField.inverseState,inverse_field_destination,
    field_header_frame _ _ _ .x6 (by decide) (by decide),field_header_skip,byte_offset_add]
  congr 2
  simp [RawField.skip,RawField.bytes]
  omega

theorem inverse_raw_field_descriptor (field : RawField) (s : MachineState) :
    (field.inverseState s).getReg .x7=s.getReg .x7+2 := by
  rw [RawField.inverseState,inverse_field_descriptor,field_header_frame _ _ _ .x7 (by decide) (by decide)]

end CommitGolfCandidate.Chained.Native
