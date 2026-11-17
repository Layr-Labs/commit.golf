import CommitGolfCandidate.CapCheckPathBranch

/-! Three concrete lower-path copies are linked to the cap checker bytes.
The odd branch first moves the current digest within scratch and then reads
the sibling; the even branch reads that sibling directly into the right half. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_path_copy_current_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check) .x21 .x21 0 32 4280 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (46+i) _ (by omega)
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_path_copy_odd_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check) .x25 .x21 0 0 4312 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (54+i) _ (by omega)
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_path_copy_even_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check) .x25 .x21 0 32 4348 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (63+i) _ (by omega)
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

def capCheckPathPreparedState (state : MachineState) : MachineState :=
  if state.getReg .x20 &&& 1 = 0 then
    capWordCopyPrefix .x25 .x21 0 32 (capCheckPathBranchState state) 8
  else
    (capWordCopyPrefix .x25 .x21 0 0
      (capWordCopyPrefix .x21 .x21 0 32 (capCheckPathBranchState state) 8) 8).setPC 4380

def capCheckPathPreparationSteps (index : Word) : Nat :=
  if index &&& 1 = 0 then 10 else 19

theorem cap_check_path_prepared_pc (state : MachineState) :
    (capCheckPathPreparedState state).pc = 4380 := by
  unfold capCheckPathPreparedState
  split
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide)]
    unfold capCheckPathBranchState
    simp only [MachineState.setPC, if_pos ‹_›]
    rfl
  · rfl

theorem cap_check_path_prepared_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7) :
    (capCheckPathPreparedState state).getReg reg = state.getReg reg := by
  unfold capCheckPathPreparedState
  split
  · rw [cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) reg outside.1,
      cap_check_path_branch_register state reg outside.2]
  · rw [MachineState.getReg_setPC,
      cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) reg outside.1,
      cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) reg outside.1,
      cap_check_path_branch_register state reg outside.2]

end CommitGolfCandidate
