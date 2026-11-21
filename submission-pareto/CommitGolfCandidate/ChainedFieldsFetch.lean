import CommitGolfCandidate.ChainedRecordFields
import CommitGolfCandidate.ChainedOpeningControllerCode

/-! Compile field-list fetch premises from a single instruction-list memory interface. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def OpsAt (image : Image) (base : Word) (ops : List Instr) : Prop :=
  ∀ index, index<ops.length → ∀ s : MachineState, s.pc=base+BitVec.ofNat 64 (4*index) →
    fetch image s=some (.base (ops.getD index .EBREAK))

theorem ops_at_left (image : Image) (base : Word) (front back : List Instr)
    (code : OpsAt image base (front++back)) : OpsAt image base front := by
  intro index inside s pc
  have result := code index (by simp only [List.length_append]; omega) s pc
  simpa only [List.getD_append front back .EBREAK index inside] using result

theorem ops_at_right (image : Image) (base : Word) (front back : List Instr)
    (code : OpsAt image base (front++back)) :
    OpsAt image (base+BitVec.ofNat 64 (4*front.length)) back := by
  intro index inside s pc
  have location : s.pc=base+BitVec.ofNat 64 (4*(front.length+index)) := by
    rw [pc,byte_offset_add]
    congr 2
    omega
  have result := code (front.length+index) (by simp only [List.length_append]; omega) s location
  simpa only [List.getD_append_right front back .EBREAK (front.length+index) (by omega),Nat.add_sub_cancel_left] using result

def fieldBuildOps (n : Nat) : List Instr := List.ofFn fun i : Fin (4*n+5) => fieldBuildOp n i.val
def rawFieldOps (field : RawField) : List Instr := fieldHeaderOps field.skip field.width++fieldBuildOps field.low.length
def rawFieldsOps (fields : List RawField) : List Instr := fields.flatMap rawFieldOps

theorem raw_field_ops_length (field : RawField) : (rawFieldOps field).length=rawFieldSteps field := by
  simp only [rawFieldOps,fieldHeaderOps,fieldBuildOps,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,rawFieldSteps]
  omega

theorem field_build_ops_get (n index : Nat) (inside : index<4*n+5) :
    (fieldBuildOps n).getD index .EBREAK=fieldBuildOp n index := by
  simp only [fieldBuildOps,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left inside,Option.getD_some]

theorem raw_field_at_of_ops (image : Image) (base : Word) (field : RawField)
    (code : OpsAt image base (rawFieldOps field)) : RawFieldAt image base field := by
  have header := ops_at_left image base _ _ code
  have body := ops_at_right image base _ _ code
  change OpsAt image (base+8) (fieldBuildOps field.low.length) at body
  refine ⟨?_,?_,?_⟩
  · intro i s pc
    exact header i.val i.isLt s pc
  · intro index inside i s pc
    have bound : 4*index+i.val<4*field.low.length := by have := i.isLt; omega
    have location : s.pc=(base+8)+BitVec.ofNat 64 (4*(4*index+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*index+i.val) (by simp only [fieldBuildOps,List.length_ofFn]; omega) s location
    have same : fieldBuildOp field.low.length (4*index+i.val)=byteCopyOp i.val := by
      have remainder : (4*index+i.val)%4=i.val := by have := i.isLt; omega
      simp only [fieldBuildOp,ite_eq_left bound,remainder]
    simpa only [field_build_ops_get field.low.length (4*index+i.val) (by omega),same] using result
  · intro i s pc
    have location : s.pc=(base+8)+BitVec.ofNat 64 (4*(4*field.low.length+i.val)) := by
      rw [pc,byte_offset_add]
      congr 2
      omega
    have result := body (4*field.low.length+i.val) (by simp only [fieldBuildOps,List.length_ofFn]; have := i.isLt; omega) s location
    have same : fieldBuildOp field.low.length (4*field.low.length+i.val)=fieldDescriptorOp i.val := by
      simp [fieldBuildOp]
    simpa only [field_build_ops_get field.low.length (4*field.low.length+i.val) (by have := i.isLt; omega),same] using result

theorem raw_fields_at_of_ops (image : Image) (base : Word) (fields : List RawField)
    (code : OpsAt image base (rawFieldsOps fields)) : RawFieldsAt image base fields := by
  induction fields generalizing base with
  | nil => trivial
  | cons field fields ih =>
    change OpsAt image base (rawFieldOps field++rawFieldsOps fields) at code
    refine ⟨raw_field_at_of_ops image base field (ops_at_left image base _ _ code),?_⟩
    have tailCode := ops_at_right image base _ _ code
    rw [raw_field_ops_length] at tailCode
    exact ih _ tailCode

end CommitGolfCandidate.Chained.Native
