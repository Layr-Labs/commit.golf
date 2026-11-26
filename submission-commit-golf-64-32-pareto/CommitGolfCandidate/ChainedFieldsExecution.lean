import CommitGolfCandidate.ChainedFieldsMemory

/-! Actual execution and exact charges for complete native field-list construction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def rawFieldSteps (field : RawField) : Nat := 4*field.low.length+7
def rawFieldsSteps : List RawField → Nat
  | [] => 0
  | field::fields => rawFieldSteps field+rawFieldsSteps fields

def RawFieldAt (image : Image) (base : Word) (field : RawField) : Prop :=
  FieldHeaderAt image base field.skip field.width ∧
  LowCopyAt image (base+8) field.low.length ∧
  FieldDescriptorAt image ((base+8)+BitVec.ofNat 64 (16*field.low.length))

def RawFieldsAt (image : Image) : Word → List RawField → Prop
  | _,[] => True
  | base,field::fields => RawFieldAt image base field ∧
      RawFieldsAt image (base+BitVec.ofNat 64 (4*rawFieldSteps field)) fields

theorem raw_field_pc (field : RawField) (s : MachineState) :
    (field.state s).pc=s.pc+BitVec.ofNat 64 (4*rawFieldSteps field) := by
  rw [RawField.state,preparedFieldState,field_build_pc,field_header_pc _ _ _ 2 (by decide)]
  change (s.pc+BitVec.ofNat 64 8)+BitVec.ofNat 64 (4*(4*field.low.length+5))=_
  rw [byte_offset_add]
  unfold rawFieldSteps
  congr 2
  omega

theorem raw_fields_steps (fields : List RawField) :
    rawFieldsSteps fields=4*(rawFieldsLow fields).length+7*fields.length := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    change rawFieldSteps field+rawFieldsSteps fields=4*(field.low++rawFieldsLow fields).length+7*(field::fields).length
    rw [ih]
    simp only [rawFieldSteps,List.length_append,List.length_cons,Nat.mul_add]
    omega

theorem raw_fields_execution (image : Image) (fields : List RawField)
    (suffix outputPrefix metaPrefix : Proof) (s : MachineState) (source outputBase metaBase : Nat)
    (base : Word) (code : RawFieldsAt image base fields)
    (ready : RawFieldsReady fields suffix outputPrefix metaPrefix s source outputBase metaBase)
    (pc : s.pc=base) (capacity : metaBase+metaPrefix.length+2*fields.length≤MEMORY_BYTES)
    (fuel : Nat) (coins : Bool) :
    execute image (rawFieldsSteps fields+fuel) s coins=
      (do let result ← execute image fuel (rawFieldsState fields s) coins
          return result.charge (rawFieldsSteps fields) 0) := by
  induction fields generalizing s source base outputPrefix metaPrefix with
  | nil => simp [rawFieldsSteps,raw_fields_zero,Execution.charge]
  | cons field fields ih =>
    have sourceRoom : source+field.low.length+1≤metaBase := by
      have bound := ready.separate
      change source+(field.bytes++rawFieldsBytes fields).length+suffix.length≤metaBase at bound
      simp only [RawField.bytes,List.length_append,List.length_cons] at bound
      omega
    have ordered := ready.ordered
    have room := ready.room
    have sourceNumber : (s.getReg .x5).toNat=source := by
      rw [ready.sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have outputNumber : (s.getReg .x6).toNat=outputBase+outputPrefix.length := by
      rw [ready.outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have metaNumber : (s.getReg .x7).toNat=metaBase+metaPrefix.length := by
      rw [ready.metaPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have sourceAccess : (s.getReg .x5).toNat+field.low.length+1≤MEMORY_BYTES := by
      rw [sourceNumber]
      omega
    have outputAccess : (s.getReg .x6).toNat+field.low.length≤MEMORY_BYTES := by
      rw [outputNumber]
      omega
    have metaAccess : (s.getReg .x7).toNat+2≤MEMORY_BYTES := by
      rw [metaNumber]
      simp only [List.length_cons] at capacity
      omega
    have next := raw_fields_step field fields suffix outputPrefix metaPrefix s source outputBase metaBase ready
    have nextPC : (field.state s).pc=base+BitVec.ofNat 64 (4*rawFieldSteps field) := by rw [raw_field_pc,pc]
    have nextCapacity : metaBase+(metaPrefix++descriptorBytes [field.high]).length+2*fields.length≤MEMORY_BYTES := by
      simp only [List.length_append,descriptor_bytes_length,List.length_cons,List.length_nil] at capacity ⊢
      omega
    have tailRun := ih (outputPrefix:=outputPrefix++field.low) (metaPrefix:=metaPrefix++descriptorBytes [field.high])
      (s:=field.state s) (source:=source+field.bytes.length)
      (base:=base+BitVec.ofNat 64 (4*rawFieldSteps field)) code.2 next nextPC nextCapacity
    have count : rawFieldsSteps (field::fields)+fuel=(4*field.low.length+7)+(rawFieldsSteps fields+fuel) := by
      change rawFieldSteps field+rawFieldsSteps fields+fuel=_
      unfold rawFieldSteps
      omega
    rw [count,prepared_field_execution image base field.skip field.width field.low.length
      code.1.1 code.1.2.1 code.1.2.2 s pc sourceAccess outputAccess metaAccess]
    change (do let result ← execute image (rawFieldsSteps fields+fuel) (field.state s) coins
               return result.charge (4*field.low.length+7) 0)=_
    rw [tailRun]
    simp [rawFieldsSteps,rawFieldSteps,raw_fields_cons,Execution.charge,
      bind_assoc,pure_bind,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem raw_field_control (field : RawField) (s : MachineState) :
    (field.state s).getReg .x5=s.getReg .x5+BitVec.ofNat 64 field.bytes.length ∧
    (field.state s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 field.low.length ∧
    (field.state s).getReg .x7=s.getReg .x7+2 := by
  constructor
  · rw [RawField.state,preparedFieldState,field_build_source,
      field_header_frame _ _ _ .x5 (by decide) (by decide),field_header_skip,
      BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    simp only [RawField.skip,RawField.bytes,List.length_append,List.length_cons]
    omega
  · constructor
    · rw [RawField.state,preparedFieldState,field_build_destination,
        field_header_frame _ _ _ .x6 (by decide) (by decide)]
    · rw [RawField.state,preparedFieldState,field_build_descriptor_pointer,
        field_header_frame _ _ _ .x7 (by decide) (by decide)]

theorem raw_fields_control (fields : List RawField) (s : MachineState) :
    (rawFieldsState fields s).getReg .x5=s.getReg .x5+BitVec.ofNat 64 (rawFieldsBytes fields).length ∧
    (rawFieldsState fields s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 (rawFieldsLow fields).length ∧
    (rawFieldsState fields s).getReg .x7=s.getReg .x7+BitVec.ofNat 64 (2*fields.length) := by
  induction fields generalizing s with
  | nil => simp [raw_fields_zero,rawFieldsBytes,rawFieldsLow]
  | cons field fields ih =>
    rw [raw_fields_cons]
    obtain ⟨source,output,metadata⟩ := ih (field.state s)
    obtain ⟨firstSource,firstOutput,firstMetadata⟩ := raw_field_control field s
    refine ⟨?_,?_,?_⟩
    · rw [source,firstSource,BitVec.add_assoc,←BitVec.ofNat_add]
      simp only [rawFieldsBytes,List.flatMap_cons,List.length_append]
    · rw [output,firstOutput,BitVec.add_assoc,←BitVec.ofNat_add]
      simp only [rawFieldsLow,List.flatMap_cons,List.length_append]
    · rw [metadata,firstMetadata]
      have two : (2 : Word)=BitVec.ofNat 64 2 := by decide
      rw [two,BitVec.add_assoc,←BitVec.ofNat_add]
      congr 2
      simp only [List.length_cons]
      omega

theorem raw_fields_range_execution (image : Image) (fields : List RawField)
    (s : MachineState) (source output metadata : Nat) (base : Word)
    (code : RawFieldsAt image base fields) (pc : s.pc=base)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (sourceRoom : source+(rawFieldsBytes fields).length≤MEMORY_BYTES)
    (outputRoom : output+(rawFieldsLow fields).length≤MEMORY_BYTES)
    (metaRoom : metadata+2*fields.length≤MEMORY_BYTES)
    (fuel : Nat) (coins : Bool) :
    execute image (rawFieldsSteps fields+fuel) s coins=
      (do let result ← execute image fuel (rawFieldsState fields s) coins
          return result.charge (rawFieldsSteps fields) 0) := by
  induction fields generalizing s source output metadata base with
  | nil => simp [rawFieldsSteps,raw_fields_zero,Execution.charge]
  | cons field fields ih =>
    have sourceSize : (rawFieldsBytes (field::fields)).length=
        field.bytes.length+(rawFieldsBytes fields).length := by
      simp only [rawFieldsBytes,List.flatMap_cons,List.length_append]
    have outputSize : (rawFieldsLow (field::fields)).length=
        field.low.length+(rawFieldsLow fields).length := by
      simp only [rawFieldsLow,List.flatMap_cons,List.length_append]
    have rawSize : field.bytes.length=field.low.length+1+field.padding.length := by
      simp only [RawField.bytes,List.length_append,List.length_cons]
      omega
    rw [sourceSize] at sourceRoom
    rw [outputSize] at outputRoom
    simp only [List.length_cons] at metaRoom
    have sourceNumber : (s.getReg .x5).toNat=source := by
      rw [sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at sourceRoom
      omega
    have outputNumber : (s.getReg .x6).toNat=output := by
      rw [outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at outputRoom
      omega
    have metaNumber : (s.getReg .x7).toNat=metadata := by
      rw [metaPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      unfold MEMORY_BYTES at metaRoom
      omega
    obtain ⟨nextSource,nextOutput,nextMetadata⟩ := raw_field_control field s
    rw [sourcePointer,←BitVec.ofNat_add] at nextSource
    rw [outputPointer,←BitVec.ofNat_add] at nextOutput
    have two : (2 : Word)=BitVec.ofNat 64 2 := by decide
    rw [metaPointer,two,←BitVec.ofNat_add] at nextMetadata
    have nextPC : (field.state s).pc=base+BitVec.ofNat 64 (4*rawFieldSteps field) := by
      rw [raw_field_pc,pc]
    have tailRun := ih (field.state s) (source+field.bytes.length)
      (output+field.low.length) (metadata+2) (base+BitVec.ofNat 64 (4*rawFieldSteps field))
      code.2 nextPC nextSource nextOutput nextMetadata (by omega) (by omega) (by omega)
    rw [show rawFieldsSteps (field::fields)+fuel=
        (4*field.low.length+7)+(rawFieldsSteps fields+fuel) by
          simp only [rawFieldsSteps,rawFieldSteps]; omega,
      prepared_field_execution image base field.skip field.width field.low.length
        code.1.1 code.1.2.1 code.1.2.2 s pc
        (by rw [sourceNumber]; omega) (by rw [outputNumber]; omega) (by rw [metaNumber]; omega)]
    change (do let result ← execute image (rawFieldsSteps fields+fuel) (field.state s) coins
               return result.charge (4*field.low.length+7) 0)=_
    rw [tailRun]
    simp [rawFieldsSteps,rawFieldSteps,raw_fields_cons,Execution.charge,
      bind_assoc,pure_bind,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Chained.Native
