import CommitGolfCandidate.ChainedOpeningEntry

/-! The actual zero-record entry skips traversal and returns an empty successful proof. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne
@[local simp] private theorem empty_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem empty_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def openingEmptyOps : List Instr :=
  [.JAL .x0 8956,.SUB .x11 .x6 .x17,.ADDI .x5 .x0 1,.ADDI .x10 .x0 0]
def openingEmptyPrefix (s : MachineState) (count : Nat) : MachineState :=
  (openingEmptyOps.take count).foldl execInstrBr s

theorem opening_empty_pc (s : MachineState) (count : Nat) (small : count≤4) :
    (openingEmptyPrefix s count).pc=if count=0 then s.pc else s.pc+BitVec.ofNat 64 (8952+4*count) := by
  interval_cases count <;> simp [openingEmptyPrefix,openingEmptyOps,execInstrBr,signExtend12,signExtend21,BitVec.add_assoc]

theorem opening_empty_byte (s : MachineState) (query : Word) :
    (openingEmptyPrefix s 4).getByte query=s.getByte query := rfl

theorem opening_empty_length (s : MachineState) :
    (openingEmptyPrefix s 4).getReg .x11=s.getReg .x6-s.getReg .x17 := by
  simp [openingEmptyPrefix,openingEmptyOps,execInstrBr,signExtend12]

theorem opening_empty_execution (s : MachineState) (pc : s.pc=4116) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (5+fuel) s coins=pure ⟨.success,openingEmptyPrefix s 4,5,0⟩ := by
  have block (rest : Nat) : execute openingControllerImage (4+rest) s coins=
      (do let result ← execute openingControllerImage rest (openingEmptyPrefix s 4) coins
          return result.charge 4 0) := by
    apply execute_unit_steps (states := openingEmptyPrefix s)
    intro index inside
    refine ⟨.base (openingEmptyOps.getD index .EBREAK),?_,?_,?_⟩
    · interval_cases index
      · exact opening_controller_ops_at 5 (by rw [opening_controller_ops_length]; decide) s pc
      · exact controller_opening_finish_at 1 (by decide) _ (by rw [opening_empty_pc _ 1 (by decide),pc]; rfl)
      · exact controller_opening_finish_at 2 (by decide) _ (by rw [opening_empty_pc _ 2 (by decide),pc]; rfl)
      · exact controller_opening_finish_at 3 (by decide) _ (by rw [opening_empty_pc _ 3 (by decide),pc]; rfl)
    · interval_cases index <;> rfl
    · interval_cases index <;> rfl
  have fetched : fetch openingControllerImage (openingEmptyPrefix s 4)=some (.base .ECALL) :=
    controller_opening_finish_at 4 (by decide) _ (by rw [opening_empty_pc _ 4 (by decide),pc]; rfl)
  have halt : (openingEmptyPrefix s 4).getReg .x5=1 := rfl
  have success : (openingEmptyPrefix s 4).getReg .x10=0 := rfl
  rw [show 5+fuel=4+(fuel+1) by omega,block]
  unfold execute
  rw [fetched]
  simp only [halt,success]
  rfl

theorem opening_entry_empty (s : MachineState) (pc : s.pc=4096) (empty : s.getReg .x16=0#64) :
    ∃ after, (∀ fuel coins, execute openingControllerImage (10+fuel) s coins=pure ⟨.success,after,10,0⟩) ∧
      after.getReg .x11=0#64 ∧ ∀ query, after.getByte query=s.getByte query := by
  have entryPC : (openingEntryPrefix s 5).pc=4116 := by
    simp [openingEntryPrefix,openingEntryOps,execInstrBr,signExtend12,signExtend13,pc,empty]
  refine ⟨openingEmptyPrefix (openingEntryPrefix s 5) 4,?_,?_,?_⟩
  · intro fuel coins
    rw [show 10+fuel=5+(5+fuel) by omega,opening_entry_execution s pc,
      opening_empty_execution _ entryPC]
    rfl
  · rw [opening_empty_length,(opening_entry_data s).2.1,(opening_entry_data s).2.2.1,BitVec.sub_self]
  · intro query
    rw [opening_empty_byte,opening_entry_byte]

end CommitGolfCandidate.Chained.Native
