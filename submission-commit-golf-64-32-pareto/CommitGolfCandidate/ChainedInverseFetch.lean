import CommitGolfCandidate.ChainedInversePayload
import CommitGolfCandidate.ChainedRecordFetch

/-! Compile inverse field fetch premises from value-independent instruction shapes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def inverseFieldOp (n index : Nat) : Instr :=
  if index<4*n then byteCopyOp (index%4) else inverseFieldTailOp (index-4*n)
def inverseFieldOps (n : Nat) : List Instr := List.ofFn fun i : Fin (4*n+4) => inverseFieldOp n i.val
def inverseRawFieldOps (field : RawField) : List Instr :=
  fieldHeaderOps field.skip field.width++inverseFieldOps field.low.length
def inverseRawFieldsOps (fields : List RawField) : List Instr := fields.flatMap inverseRawFieldOps

theorem inverse_raw_field_ops_length (field : RawField) :
    (inverseRawFieldOps field).length=inverseRawFieldSteps field := by
  simp only [inverseRawFieldOps,fieldHeaderOps,inverseFieldOps,List.length_append,List.length_cons,
    List.length_nil,List.length_ofFn,inverseRawFieldSteps]
  omega

theorem inverse_field_ops_get (n index : Nat) (inside : index<4*n+4) :
    (inverseFieldOps n).getD index .EBREAK=inverseFieldOp n index := by
  simp only [inverseFieldOps,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left inside,Option.getD_some]

theorem inverse_raw_field_at_of_ops (image : Image) (base : Word) (field : RawField)
    (code : OpsAt image base (inverseRawFieldOps field)) : InverseRawFieldAt image base field := by
  have header := ops_at_left image base _ _ code
  have body := ops_at_right image base _ _ code
  change OpsAt image (base+8) (inverseFieldOps field.low.length) at body
  refine ⟨?_,?_,?_⟩
  · intro i s pc
    exact header i.val i.isLt s pc
  · intro index inside i s pc
    have bound : 4*index+i.val<4*field.low.length := by have := i.isLt; omega
    have location : s.pc=(base+8)+BitVec.ofNat 64 (4*(4*index+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*index+i.val) (by simp only [inverseFieldOps,List.length_ofFn]; omega) s location
    have same : inverseFieldOp field.low.length (4*index+i.val)=byteCopyOp i.val := by
      have remainder : (4*index+i.val)%4=i.val := by have := i.isLt; omega
      simp only [inverseFieldOp,ite_eq_left bound,remainder]
    simpa only [inverse_field_ops_get field.low.length (4*index+i.val) (by omega),same] using result
  · intro i s pc
    have location : s.pc=(base+8)+BitVec.ofNat 64 (4*(4*field.low.length+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*field.low.length+i.val)
      (by simp only [inverseFieldOps,List.length_ofFn]; have := i.isLt; omega) s location
    have same : inverseFieldOp field.low.length (4*field.low.length+i.val)=inverseFieldTailOp i.val := by
      simp [inverseFieldOp]
    simpa only [inverse_field_ops_get field.low.length (4*field.low.length+i.val)
      (by have := i.isLt; omega),same] using result

theorem inverse_raw_fields_at_of_ops (image : Image) (base : Word) (fields : List RawField)
    (code : OpsAt image base (inverseRawFieldsOps fields)) : InverseRawFieldsAt image base fields := by
  induction fields generalizing base with
  | nil => trivial
  | cons field fields ih =>
    change OpsAt image base (inverseRawFieldOps field++inverseRawFieldsOps fields) at code
    refine ⟨inverse_raw_field_at_of_ops image base field (ops_at_left image base _ _ code),?_⟩
    have tailCode := ops_at_right image base _ _ code
    rw [inverse_raw_field_ops_length] at tailCode
    exact ih _ tailCode

def inverseFieldShapeOps (shape : FieldShape) : List Instr :=
  [.ADDI .x9 .x0 (BitVec.ofNat 12 (1+shape.2.1)),.ADDI .x10 .x0 (BitVec.ofNat 12 shape.2.2)]++
    inverseFieldOps shape.1

theorem inverse_raw_fields_ops_shapes (fields : List RawField) :
    inverseRawFieldsOps fields=(fields.map rawFieldShape).flatMap inverseFieldShapeOps := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    change inverseRawFieldOps field++inverseRawFieldsOps fields=inverseFieldShapeOps (rawFieldShape field)++_
    rw [ih]
    rfl

def inverseRecordPlanOps : List Instr :=
  (specFieldShapes InteriorCodec.recordSpec recordSourcePads).flatMap inverseFieldShapeOps

theorem inverse_record_raw_fields_ops (record : InteriorCodec.Record) :
    inverseRawFieldsOps (recordRawFields record)=inverseRecordPlanOps := by
  rw [inverse_raw_fields_ops_shapes]
  unfold recordRawFields
  rw [payload_raw_fields_shapes]
  rfl

end CommitGolfCandidate.Chained.Native
