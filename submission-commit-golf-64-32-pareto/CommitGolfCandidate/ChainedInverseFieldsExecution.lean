import CommitGolfCandidate.ChainedInverseFieldsMemory

/-! Actual execution and exact charges for whole-payload field reconstruction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def inverseRawFieldSteps (field : RawField) : Nat := 4*field.low.length+6
def inverseRawFieldsSteps : List RawField → Nat
  | [] => 0
  | field::fields => inverseRawFieldSteps field+inverseRawFieldsSteps fields

def InverseRawFieldAt (image : Image) (base : Word) (field : RawField) : Prop :=
  FieldHeaderAt image base field.skip field.width ∧
  LowCopyAt image (base+8) field.low.length ∧
  InverseFieldTailAt image ((base+8)+BitVec.ofNat 64 (16*field.low.length))

def InverseRawFieldsAt (image : Image) : Word → List RawField → Prop
  | _,[] => True
  | base,field::fields => InverseRawFieldAt image base field ∧
    InverseRawFieldsAt image (base+BitVec.ofNat 64 (4*inverseRawFieldSteps field)) fields

theorem inverse_raw_field_pc (field : RawField) (s : MachineState) :
    (field.inverseState s).pc=s.pc+BitVec.ofNat 64 (4*inverseRawFieldSteps field) := by
  rw [RawField.inverseState,inverseFieldState,inverse_field_tail_pc _ 4 (by decide),low_copy_pc,
    field_header_pc _ _ _ 2 (by decide)]
  change ((s.pc+BitVec.ofNat 64 8)+BitVec.ofNat 64 (16*field.low.length))+BitVec.ofNat 64 16=_
  rw [byte_offset_add,byte_offset_add]
  congr 2
  unfold inverseRawFieldSteps
  omega

theorem inverse_raw_fields_steps (fields : List RawField) :
    inverseRawFieldsSteps fields=4*(rawFieldsLow fields).length+6*fields.length := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    change inverseRawFieldSteps field+inverseRawFieldsSteps fields=
      4*(field.low++rawFieldsLow fields).length+6*(field::fields).length
    rw [ih]
    simp only [inverseRawFieldSteps,List.length_append,List.length_cons,Nat.mul_add]
    omega

theorem inverse_prepared_field_execution (image : Image) (base : Word) (field : RawField)
    (code : InverseRawFieldAt image base field) (s : MachineState) (pc : s.pc=base)
    (source : (s.getReg .x5).toNat+field.low.length+1≤MEMORY_BYTES)
    (destination : (s.getReg .x6).toNat+field.low.length+1≤MEMORY_BYTES)
    (scratch : (s.getReg .x7).toNat+2≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute image (inverseRawFieldSteps field+fuel) s coins=
      (do let result ← execute image fuel (field.inverseState s) coins
          return result.charge (inverseRawFieldSteps field) 0) := by
  let state := fieldHeaderPrefix field.skip field.width s 2
  have inputRoom : (state.getReg .x5).toNat+field.low.length+1≤MEMORY_BYTES := by
    simpa only [state,field_header_frame _ _ _ .x5 (by decide) (by decide)] using source
  have outputRoom : (state.getReg .x6).toNat+field.low.length+1≤MEMORY_BYTES := by
    simpa only [state,field_header_frame _ _ _ .x6 (by decide) (by decide)] using destination
  have metaRoom : (state.getReg .x7).toNat+2≤MEMORY_BYTES := by
    simpa only [state,field_header_frame _ _ _ .x7 (by decide) (by decide)] using scratch
  have ready := field_build_access field.low.length state inputRoom (by omega) metaRoom
  have output : accessValid ((lowCopyState field.low.length state).getReg .x6) 1=true := by
    rw [low_copy_destination]
    exact byte_access_offset _ _ outputRoom
  have nextPC : state.pc=base+8 := by
    rw [field_header_pc _ _ _ 2 (by decide),pc]
    rfl
  rw [show inverseRawFieldSteps field+fuel=2+(4*field.low.length+4+fuel) by unfold inverseRawFieldSteps; omega,
    field_header_execution image base field.skip field.width code.1 s pc,
    inverse_field_execution image (base+8) field.low.length code.2.1 code.2.2 state nextPC
      ready.1 ready.2.2.1 output]
  simp [RawField.inverseState,state,inverseRawFieldSteps,Execution.charge,
    Nat.add_comm,Nat.add_left_comm]
  simp only [show 2+(4+4*field.low.length)=6+4*field.low.length by omega]

theorem inverse_raw_fields_execution (image : Image) (fields : List RawField)
    (suffix completed : Proof) (s : MachineState) (source outputBase metadata : Nat)
    (base : Word) (code : InverseRawFieldsAt image base fields)
    (ready : InverseFieldsReady fields suffix completed s source outputBase metadata)
    (pc : s.pc=base) (capacity : metadata+2*fields.length≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute image (inverseRawFieldsSteps fields+fuel) s coins=
      (do let result ← execute image fuel (inverseRawFieldsState fields s) coins
          return result.charge (inverseRawFieldsSteps fields) 0) := by
  induction fields generalizing s source metadata base completed with
  | nil => simp [inverseRawFieldsSteps,inverse_raw_fields_zero,Execution.charge]
  | cons field fields ih =>
    have sourceBound := ready.inputBefore
    change source+(field.low++rawFieldsLow fields).length+suffix.length<outputBase at sourceBound
    rw [List.length_append] at sourceBound
    have outputBound := ready.outputBefore
    change outputBase+completed.length+(field.bytes++rawFieldsBytes fields).length≤metadata at outputBound
    simp only [RawField.bytes,List.length_append,List.length_cons] at outputBound
    have room := ready.room
    simp only [List.length_cons] at room capacity
    have sourceNumber : (s.getReg .x5).toNat=source := by
      rw [ready.sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have outputNumber : (s.getReg .x6).toNat=outputBase+completed.length := by
      rw [ready.outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have metaNumber : (s.getReg .x7).toNat=metadata := by
      rw [ready.metaPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have sourceAccess : (s.getReg .x5).toNat+field.low.length+1≤MEMORY_BYTES := by rw [sourceNumber]; omega
    have outputAccess : (s.getReg .x6).toNat+field.low.length+1≤MEMORY_BYTES := by rw [outputNumber]; omega
    have metaAccess : (s.getReg .x7).toNat+2≤MEMORY_BYTES := by rw [metaNumber]; omega
    have next := inverse_fields_step field fields suffix completed s source outputBase metadata ready
    have nextPC : (field.inverseState s).pc=base+BitVec.ofNat 64 (4*inverseRawFieldSteps field) := by
      rw [inverse_raw_field_pc,pc]
    have rest := ih (completed++field.bytes) (field.inverseState s) (source+field.low.length) (metadata+2)
      (base+BitVec.ofNat 64 (4*inverseRawFieldSteps field)) code.2 next nextPC (by omega)
    rw [show inverseRawFieldsSteps (field::fields)+fuel=
        inverseRawFieldSteps field+(inverseRawFieldsSteps fields+fuel) by
          change inverseRawFieldSteps field+inverseRawFieldsSteps fields+fuel=_
          omega,
      inverse_prepared_field_execution image base field code.1 s pc sourceAccess outputAccess metaAccess,
      rest,inverse_raw_fields_cons]
    simp [inverseRawFieldsSteps,Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
