import CommitGolfCandidate.ChainedInverseFieldsReady

/-! Whole-list native reconstruction preserves completed output and unread input. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

@[irreducible] def inverseRawFieldsState : List RawField → MachineState → MachineState
  | [],s => s
  | field::fields,s => inverseRawFieldsState fields (field.inverseState s)

theorem inverse_raw_fields_zero (s : MachineState) : inverseRawFieldsState [] s=s := by
  unfold inverseRawFieldsState
  rfl

theorem inverse_raw_fields_cons (field : RawField) (fields : List RawField) (s : MachineState) :
    inverseRawFieldsState (field::fields) s=inverseRawFieldsState fields (field.inverseState s) := by
  conv => lhs; unfold inverseRawFieldsState

theorem inverse_raw_fields_memory (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady fields suffix completed s source outputBase metadata) :
    InverseFieldsReady [] suffix (completed++rawFieldsBytes fields)
      (inverseRawFieldsState fields s) (source+(rawFieldsLow fields).length)
      outputBase (metadata+2*fields.length) := by
  induction fields generalizing s source metadata completed with
  | nil =>
    simpa only [inverse_raw_fields_zero,rawFieldsLow,rawFieldsBytes,List.flatMap_nil,
      List.length_nil,List.append_nil,Nat.add_zero,Nat.mul_zero] using ready
  | cons field fields ih =>
    have next := inverse_fields_step field fields suffix completed s source outputBase metadata ready
    have result := ih (completed++field.bytes) (field.inverseState s) (source+field.low.length) (metadata+2) next
    simpa only [inverse_raw_fields_cons,rawFieldsLow,rawFieldsBytes,List.flatMap_cons,List.length_append,
      List.length_cons,List.append_assoc,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using result

end CommitGolfCandidate.Chained.Native
