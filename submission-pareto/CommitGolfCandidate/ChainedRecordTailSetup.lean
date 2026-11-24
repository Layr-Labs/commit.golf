import CommitGolfCandidate.ChainedRecordFetch
import CommitGolfCandidate.ChainedPayloadExecution
import CommitGolfCandidate.ChainedTailAccess

/-! Actual record-tail register setup and traversal fetches in the standalone opener. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[local simp] private theorem setup_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def recordTailSetupOps : List Instr :=
  [.ADDI .x20 .x6 0,.ADDI .x21 .x7 4062,.ADDI .x22 .x0 17,
   .ADDI .x23 .x0 0,.ADDI .x25 .x0 0,.ADDI .x27 .x0 8]
def recordTailSetupPrefix (s : MachineState) (count : Nat) : MachineState :=
  (recordTailSetupOps.take count).foldl execInstrBr s

theorem record_tail_setup_cursor (s : MachineState) : (recordTailSetupPrefix s 6).getReg .x20=s.getReg .x6 := by
  change s.getReg .x6+0=s.getReg .x6
  exact BitVec.add_zero _
theorem record_tail_setup_source (s : MachineState) : (recordTailSetupPrefix s 6).getReg .x21=s.getReg .x7-34 := by
  change s.getReg .x7+signExtend12 4062=s.getReg .x7-34
  rw [BitVec.sub_eq_add_neg]
  rfl
theorem record_tail_setup_count (s : MachineState) : (recordTailSetupPrefix s 6).getReg .x22=17 := rfl
theorem record_tail_setup_buffer (s : MachineState) : TailBuffer (recordTailSetupPrefix s 6) [] := by
  exact ⟨rfl,rfl,rfl,by decide⟩
theorem record_tail_setup_byte (s : MachineState) (query : Word) :
    (recordTailSetupPrefix s 6).getByte query=s.getByte query := rfl
theorem record_tail_setup_frame (s : MachineState) (reg : Reg)
    (a : reg≠.x20) (b : reg≠.x21) (c : reg≠.x22) (d : reg≠.x23) (e : reg≠.x25) (f : reg≠.x27) :
    (recordTailSetupPrefix s 6).getReg reg=s.getReg reg := by
  cases reg <;> first | contradiction | rfl

theorem record_tail_setup_pc (s : MachineState) (count : Nat) (small : count≤6) :
    (recordTailSetupPrefix s count).pc=s.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [recordTailSetupPrefix,recordTailSetupOps,execInstrBr,BitVec.add_assoc]

theorem record_tail_setup_execution (image : Image) (base : Word)
    (code : OpsAt image base recordTailSetupOps) (s : MachineState) (pc : s.pc=base)
    (fuel : Nat) (coins : Bool) :
    execute image (6+fuel) s coins=
      (do let result ← execute image fuel (recordTailSetupPrefix s 6) coins
          return result.charge 6 0) := by
  apply execute_unit_steps (states:=recordTailSetupPrefix s)
  intro i inside
  refine ⟨.base (recordTailSetupOps.getD i .EBREAK),?_,?_,?_⟩
  · apply code i inside
    rw [record_tail_setup_pc s i (by omega),pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem opening_record_tail_layout : openingControllerOps=
    openingControllerOps.take 2044++(recordTailSetupOps++tailTraverseOps)++openingControllerOps.drop 2067 := by decide

theorem controller_record_tail_at (image : Image) (base : Word) (code : OpsAt image base openingControllerOps) :
    OpsAt image (base+8176) recordTailSetupOps ∧ TailTraverseAt image (base+8200) := by
  rw [opening_record_tail_layout,List.append_assoc] at code
  have afterPrefix := ops_at_right image base (openingControllerOps.take 2044)
    ((recordTailSetupOps++tailTraverseOps)++openingControllerOps.drop 2067) code
  rw [List.length_take,opening_controller_ops_length] at afterPrefix
  have both := ops_at_left image _ _ _ afterPrefix
  have setup := ops_at_left image _ _ _ both
  have traversal := ops_at_right image _ _ _ both
  change OpsAt image (base+8176) recordTailSetupOps at setup
  change OpsAt image ((base+8176)+24) tailTraverseOps at traversal
  have location : (base+8176)+24=base+8200 := by rw [BitVec.add_assoc]; rfl
  rw [location] at traversal
  refine ⟨setup,?_⟩
  intro i s pc
  exact traversal i.val i.isLt s pc

theorem raw_fields_end_pc (fields : List RawField) (s : MachineState) :
    (rawFieldsState fields s).pc=s.pc+BitVec.ofNat 64 (4*rawFieldsSteps fields) := by
  induction fields generalizing s with
  | nil => simp [raw_fields_zero,rawFieldsSteps]
  | cons field fields ih =>
    rw [raw_fields_cons,ih,raw_field_pc,byte_offset_add]
    simp only [rawFieldsSteps,Nat.mul_add]

end CommitGolfCandidate.Chained.Native
