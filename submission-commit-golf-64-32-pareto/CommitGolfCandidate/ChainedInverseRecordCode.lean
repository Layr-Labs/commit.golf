import CommitGolfCandidate.ChainedInverseFetch

/-! A decoded, value-independent instruction image for complete raw-record reconstruction. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

def inverseFieldWord (n index : Nat) : BitVec 32 :=
  if index<4*n then byteCopyWords.getD (index%4) 0 else inverseFieldTailWords.getD (index-4*n) 0
def inverseFieldWords (n : Nat) : List (BitVec 32) :=
  List.ofFn fun i : Fin (4*n+4) => inverseFieldWord n i.val
def inverseFieldShapeWords (shape : FieldShape) : List (BitVec 32) :=
  [BitVec.ofNat 32 (0x00000493+1048576*(1+shape.2.1)),
   BitVec.ofNat 32 (0x00000513+1048576*shape.2.2)]++inverseFieldWords shape.1
def inverseRecordWords : List (BitVec 32) :=
  (specFieldShapes InteriorCodec.recordSpec recordSourcePads).flatMap inverseFieldShapeWords
def inverseRecordImage : Image := ⟨inverseRecordWords,[]⟩
def inverseDecodeBase (word : BitVec 32) : Option Instr :=
  match decodeInstruction word with
  | some (.base op) => some op
  | _ => none

theorem inverse_record_words_length : inverseRecordWords.length=2018 := by decide +kernel
theorem inverse_record_ops_length : inverseRecordPlanOps.length=2018 := by decide +kernel
theorem inverse_record_decode :
    inverseRecordWords.map inverseDecodeBase=inverseRecordPlanOps.map some := by decide +kernel

theorem inverse_record_decode_at (i : Fin 2018) :
    (inverseRecordWords[i.val]?).bind decodeInstruction=
      some (.base (inverseRecordPlanOps.getD i.val .EBREAK)) := by
  have projected := congrArg (fun xs => xs[i.val]?) inverse_record_decode
  simp only [List.getElem?_map] at projected
  have op : inverseRecordPlanOps[i.val]?=some (inverseRecordPlanOps.getD i.val .EBREAK) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by rw [inverse_record_ops_length]; exact i.isLt)]
    rfl
  rw [op] at projected
  cases word : inverseRecordWords[i.val]? with
  | none => simp [word] at projected
  | some value =>
    simp only [word,Option.map_some,Option.some.injEq] at projected
    simp only [word,Option.bind_some]
    cases decoded : decodeInstruction value with
    | none => simp [inverseDecodeBase,decoded] at projected
    | some instruction =>
      cases instruction <;> simp [inverseDecodeBase,decoded] at projected <;> simp [projected]

theorem inverse_image_fetch (image : Image) (s : MachineState) (index : Nat) (op : Instr)
    (fit : 4096+4*index<2^64) (pc : s.pc=BitVec.ofNat 64 (4096+4*index))
    (decoded : (image.code[index]?).bind decodeInstruction=some (.base op)) :
    fetch image s=some (.base op) := by
  have numeric : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit]
  rw [fetch,numeric,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry,Option.bind_some] using decoded

theorem inverse_record_ops_at : OpsAt inverseRecordImage 4096 inverseRecordPlanOps := by
  intro index inside s pc
  have bound : index<2018 := by simpa only [inverse_record_ops_length] using inside
  apply inverse_image_fetch inverseRecordImage s index _ (by omega)
  · change s.pc=BitVec.ofNat 64 4096+BitVec.ofNat 64 (4*index) at pc
    rwa [←BitVec.ofNat_add] at pc
  · exact inverse_record_decode_at ⟨index,bound⟩

theorem inverse_record_fields_at (record : InteriorCodec.Record) :
    InverseRawFieldsAt inverseRecordImage 4096 (recordRawFields record) := by
  apply inverse_raw_fields_at_of_ops
  rw [inverse_record_raw_fields_ops]
  exact inverse_record_ops_at

theorem inverse_record_steps (record : InteriorCodec.Record) :
    inverseRawFieldsSteps (recordRawFields record)=2018 := by
  have low : rawFieldsLow (recordRawFields record)=lowBytes record :=
    payload_raw_fields_low record recordSourcePads record_fields_small record_pads_small
  rw [inverse_raw_fields_steps,low,record_raw_fields_count,
    (record_descriptor_sizes record).1]

theorem inverse_record_execution (record : InteriorCodec.Record) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady (recordRawFields record) suffix completed s source outputBase metadata)
    (pc : s.pc=4096) (capacity : metadata+34≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute inverseRecordImage (2018+fuel) s coins=
      (do let result ← execute inverseRecordImage fuel (inverseRawFieldsState (recordRawFields record) s) coins
          return result.charge 2018 0) := by
  have result := inverse_raw_fields_execution inverseRecordImage (recordRawFields record) suffix completed
    s source outputBase metadata 4096 (inverse_record_fields_at record) ready pc
    (by simpa only [record_raw_fields_count] using capacity) fuel coins
  simpa only [inverse_record_steps] using result

end CommitGolfCandidate.Chained.Native
