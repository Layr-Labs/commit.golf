import CommitGolfCandidate.ChainedInverseFieldsMemory

/-! Reconstruction writes only its raw-output range, independently of source contents. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem inverse_low_copy_byte_frame (n : Nat) (s : MachineState) (query : Word)
    (apart : ∀ index, index<n → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (lowCopyState n s).getByte query=s.getByte query := by
  induction n generalizing s with
  | zero => rw [low_copy_zero]
  | succ n ih =>
    rw [low_copy_succ,ih]
    · rw [byte_copy_byte,ite_eq_right (by simpa using apart 0 (by omega))]
    · intro index inside
      rw [byte_copy_destination,byte_offset_succ]
      exact apart (index+1) (by omega)

theorem inverse_raw_field_byte_frame (field : RawField) (s : MachineState) (query : Word)
    (apart : ∀ index, index<field.bytes.length → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (field.inverseState s).getByte query=s.getByte query := by
  have bound : field.low.length+1≤field.bytes.length := by simp [RawField.bytes]
  rw [RawField.inverseState,inverseFieldState,inverse_field_tail_byte,low_copy_destination,
    field_header_frame _ _ _ .x6 (by decide) (by decide),ite_eq_right (apart field.low.length (by omega))]
  rw [inverse_low_copy_byte_frame]
  · rfl
  · intro index inside
    rw [field_header_frame _ _ _ .x6 (by decide) (by decide)]
    exact apart index (by omega)

theorem inverse_raw_fields_byte_frame (fields : List RawField) (s : MachineState) (query : Word)
    (apart : ∀ index, index<(rawFieldsBytes fields).length → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (inverseRawFieldsState fields s).getByte query=s.getByte query := by
  induction fields generalizing s with
  | nil => rw [inverse_raw_fields_zero]
  | cons field fields ih =>
    have total : (rawFieldsBytes (field::fields)).length=field.bytes.length+(rawFieldsBytes fields).length := by
      change (field.bytes++rawFieldsBytes fields).length=_
      rw [List.length_append]
    rw [inverse_raw_fields_cons,ih]
    · apply inverse_raw_field_byte_frame field s query
      intro index inside
      exact apart index (by rw [total]; omega)
    · intro index inside
      rw [inverse_raw_field_destination,byte_offset_add]
      exact apart (field.bytes.length+index) (by rw [total]; omega)

theorem inverse_raw_fields_register (fields : List RawField) (s : MachineState) (reg : Reg)
    (source : reg≠.x5) (destination : reg≠.x6) (metadata : reg≠.x7)
    (skip : reg≠.x9) (width : reg≠.x10) (temporary : reg≠.x11) :
    (inverseRawFieldsState fields s).getReg reg=s.getReg reg := by
  induction fields generalizing s with
  | nil => rw [inverse_raw_fields_zero]
  | cons field fields ih =>
    rw [inverse_raw_fields_cons,ih,RawField.inverseState,
      inverse_field_frame _ _ reg source destination metadata temporary,field_header_frame _ _ _ reg skip width]

end CommitGolfCandidate.Chained.Native
