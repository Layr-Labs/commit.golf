import CommitGolfCandidate.ChainedFieldsFetch

/-! The standalone opener's actual record body implements typed native field plans. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

abbrev FieldShape := Nat × Nat × Nat
def rawFieldShape (field : RawField) : FieldShape := (field.low.length,field.padding.length,field.high.length)
def fieldShapeOps (shape : FieldShape) : List Instr :=
  [.ADDI .x9 .x0 (BitVec.ofNat 12 (1+shape.2.1)),.ADDI .x10 .x0 (BitVec.ofNat 12 shape.2.2)]++fieldBuildOps shape.1

def specFieldShapes : Spec → List Proof → List FieldShape
  | [],_ => []
  | (low,high)::spec,pads => ((low+7)/8,(pads.headD []).length,high)::specFieldShapes spec pads.tail

theorem raw_fields_ops_shapes (fields : List RawField) :
    rawFieldsOps fields=(fields.map rawFieldShape).flatMap fieldShapeOps := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
    change rawFieldOps field++rawFieldsOps fields=fieldShapeOps (rawFieldShape field)++_
    rw [ih]
    rfl

theorem payload_raw_fields_shapes {spec : Spec} (payload : Payload spec) (pads : List Proof)
    (small : ∀ field ∈ spec, field.2≤6) (padSmall : ∀ pad ∈ pads, pad.length≤2) :
    (payloadRawFields payload pads small padSmall).map rawFieldShape=specFieldShapes spec pads := by
  induction payload generalizing pads with
  | nil => rfl
  | @cons low high spec value rest ih =>
    simp only [payloadRawFields,List.map_cons,rawFieldShape,packed_bits_length,List.length_ofFn,specFieldShapes]
    rw [ih]

def recordPlanOps : List Instr := (specFieldShapes InteriorCodec.recordSpec recordSourcePads).flatMap fieldShapeOps

theorem record_raw_fields_ops (record : InteriorCodec.Record) : rawFieldsOps (recordRawFields record)=recordPlanOps := by
  rw [raw_fields_ops_shapes]
  unfold recordRawFields
  rw [payload_raw_fields_shapes]
  rfl

theorem opening_record_ops_layout : openingControllerOps=
    openingControllerOps.take 9++recordPlanOps++openingControllerOps.drop 2044 := by decide

theorem controller_record_fields_at (image : Image) (base : Word)
    (code : OpsAt image base openingControllerOps) (record : InteriorCodec.Record) :
    RawFieldsAt image (base+36) (recordRawFields record) := by
  rw [opening_record_ops_layout,List.append_assoc] at code
  have afterPrefix := ops_at_right image base (openingControllerOps.take 9)
    (recordPlanOps++openingControllerOps.drop 2044) code
  have recordCode := ops_at_left image _ _ _ afterPrefix
  change OpsAt image (base+36) recordPlanOps at recordCode
  apply raw_fields_at_of_ops
  rw [record_raw_fields_ops]
  exact recordCode

theorem opening_controller_ops_at : OpsAt openingControllerImage 4096 openingControllerOps := by
  intro index inside s pc
  apply opening_controller_fetch s ⟨index,by simpa only [opening_controller_ops_length] using inside⟩
  have start : (4096 : Word)=BitVec.ofNat 64 4096 := by decide
  rw [start,←BitVec.ofNat_add] at pc
  exact pc

theorem opening_record_fields_at (record : InteriorCodec.Record) :
    RawFieldsAt openingControllerImage 4132 (recordRawFields record) :=
  controller_record_fields_at openingControllerImage 4096 opening_controller_ops_at record

theorem opening_record_build_execution (record : InteriorCodec.Record) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (source outputBase metaBase : Nat)
    (ready : RawFieldsReady (recordRawFields record) suffix outputPrefix metaPrefix s source outputBase metaBase)
    (pc : s.pc=4132) (capacity : metaBase+metaPrefix.length+34≤MEMORY_BYTES)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (2035+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (rawFieldsState (recordRawFields record) s) coins
          return result.charge 2035 0) := by
  have result := raw_fields_execution openingControllerImage (recordRawFields record) suffix outputPrefix metaPrefix
    s source outputBase metaBase 4132 (opening_record_fields_at record) ready pc
    (by simpa only [record_raw_fields_count] using capacity) fuel coins
  simpa only [record_raw_fields_steps] using result

theorem opening_record_build_memory (record : InteriorCodec.Record) (suffix outputPrefix metaPrefix : Proof)
    (s : MachineState) (source outputBase metaBase : Nat)
    (ready : RawFieldsReady (recordRawFields record) suffix outputPrefix metaPrefix s source outputBase metaBase) :
    RawFieldsReady [] suffix (outputPrefix++lowBytes record) (metaPrefix++descriptorBytes (highRows record))
      (rawFieldsState (recordRawFields record) s) (source+498) outputBase metaBase := by
  have low : rawFieldsLow (recordRawFields record)=lowBytes record :=
    payload_raw_fields_low record recordSourcePads record_fields_small record_pads_small
  have rows : rawFieldsMeta (recordRawFields record)=descriptorBytes (highRows record) := by
    rw [raw_fields_meta_rows]
    unfold recordRawFields
    rw [payload_raw_fields_high]
  have result := raw_fields_memory (recordRawFields record) suffix outputPrefix metaPrefix s source outputBase metaBase ready
  simpa only [low,rows,record_raw_fields_length] using result

end CommitGolfCandidate.Chained.Native
