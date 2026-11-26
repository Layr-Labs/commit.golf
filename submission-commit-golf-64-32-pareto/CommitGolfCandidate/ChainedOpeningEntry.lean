import CommitGolfCandidate.ChainedPacketPacking

/-! Actual entry instructions of the standalone chained postpass. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem entry_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem entry_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def openingEntryOps : List Instr :=
  [.ADDI .x17 .x20 0,.ADDI .x5 .x20 0,.ADDI .x6 .x20 0,.ADDI .x29 .x16 0,.BNE .x16 .x0 8]
def openingEntryPrefix (s : MachineState) (count : Nat) : MachineState :=
  (openingEntryOps.take count).foldl execInstrBr s

theorem opening_entry_layout : openingControllerOps=openingEntryOps++openingControllerOps.drop 5 := by decide
theorem controller_opening_entry_at : OpsAt openingControllerImage 4096 openingEntryOps := by
  have code := opening_controller_ops_at
  rw [opening_entry_layout] at code
  exact ops_at_left openingControllerImage _ _ _ code

private theorem entry_succ (s : MachineState) (index : Nat) (inside : index<5) :
    openingEntryPrefix s (index+1)=execInstrBr (openingEntryPrefix s index) (openingEntryOps.getD index .EBREAK) := by
  interval_cases index <;> rfl

theorem opening_entry_prefix_pc (s : MachineState) (index : Nat) (inside : index≤4) :
    (openingEntryPrefix s index).pc=s.pc+BitVec.ofNat 64 (4*index) := by
  interval_cases index <;> simp [openingEntryPrefix,openingEntryOps,execInstrBr,signExtend12,BitVec.add_assoc]

theorem opening_entry_pc (s : MachineState) (pc : s.pc=4096) (nonempty : s.getReg .x16≠0#64) :
    (openingEntryPrefix s 5).pc=4120 := by
  simp [openingEntryPrefix,openingEntryOps,execInstrBr,signExtend12,signExtend13,pc,nonempty]

theorem opening_entry_data (s : MachineState) :
    (openingEntryPrefix s 5).getReg .x5=s.getReg .x20 ∧
    (openingEntryPrefix s 5).getReg .x6=s.getReg .x20 ∧
    (openingEntryPrefix s 5).getReg .x17=s.getReg .x20 ∧
    (openingEntryPrefix s 5).getReg .x29=s.getReg .x16 := by
  by_cases empty : s.getReg .x16=0#64 <;>
    simp [openingEntryPrefix,openingEntryOps,execInstrBr,signExtend12,empty]

theorem opening_entry_memory (s : MachineState) (query : Word) :
    (openingEntryPrefix s 5).getMem query=s.getMem query := by
  by_cases empty : s.getReg .x16=0#64 <;>
    simp [openingEntryPrefix,openingEntryOps,execInstrBr,signExtend12,empty]
theorem opening_entry_byte (s : MachineState) (query : Word) :
    (openingEntryPrefix s 5).getByte query=s.getByte query := by
  simp only [MachineState.getByte,opening_entry_memory]

theorem opening_entry_execution (s : MachineState) (pc : s.pc=4096) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (5+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (openingEntryPrefix s 5) coins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingEntryPrefix s)
  intro index inside
  refine ⟨.base (openingEntryOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_opening_entry_at index (by simpa [openingEntryOps] using inside)
    rw [opening_entry_prefix_pc _ index (by omega),pc]
  · rw [entry_succ s index inside]
    interval_cases index <;> rfl
  · interval_cases index <;> rfl

theorem opening_entry_ready (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState) (output : Nat)
    (pc : s.pc=4096) (nonempty : records≠[]) (count : s.getReg .x16=BitVec.ofNat 64 records.length)
    (pointer : s.getReg .x20=BitVec.ofNat 64 output)
    (memory : BytesAt s (BitVec.ofNat 64 output) (rawRecordStream records++footer))
    (separate : output+498*records.length+footer.length≤output+2^33)
    (capacity : output+2^33+34≤MEMORY_BYTES) :
    RecordStreamReady records footer (openingEntryPrefix s 5) output output (output+2^33) := by
  have small : records.length<2^64 := by omega
  have positive : 0<records.length := List.length_pos_iff_ne_nil.mpr nonempty
  have occupied : s.getReg .x16≠0#64 := by
    intro empty
    have value := congrArg BitVec.toNat empty
    rw [count,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at value
    change records.length=0 at value
    omega
  have data := opening_entry_data s
  refine ⟨?_,data.1.trans pointer,data.2.1.trans pointer,?_,data.2.2.2.trans count,?_,Nat.le_refl _,separate,capacity⟩
  · simpa only [if_neg nonempty] using opening_entry_pc s pc occupied
  · rw [data.2.2.1,pointer]
    have offset : (8589934592 : Word)=BitVec.ofNat 64 (2^33) := by decide
    rw [offset,←BitVec.ofNat_add]
  · intro index inside
    rw [opening_entry_byte]
    exact memory index inside

end CommitGolfCandidate.Chained.Native
