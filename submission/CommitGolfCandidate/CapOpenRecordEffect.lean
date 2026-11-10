import CommitGolfCandidate.CapOpenRecordTail

/-! Projections of the salt-copy continuation. The conditional instruction is
factored over an arbitrary signed offset before specializing to the actual
forward branch. All six instructions preserve memory and caller registers
apart from the cursor, heap index and lower-path counter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem final_register (state : MachineState) (reg : Reg) :
    (capOpenRecordTailPrefix state 6).getReg reg =
      (capOpenRecordTailPrefix state 5).getReg reg := by
  rw [cap_open_record_tail_succ state 5 (by decide)]
  exact branch_register _ _ reg

theorem cap_open_record_tail_memory (state : MachineState) :
    (capOpenRecordTailPrefix state 6).mem = state.mem := by
  rw [cap_open_record_tail_succ state 5 (by decide)]
  change (execInstrBr (capOpenRecordTailPrefix state 5) (.BEQ .x28 .x0 64)).mem = _
  rw [branch_memory]
  rfl

theorem cap_open_record_tail_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28) :
    (capOpenRecordTailPrefix state 6).getReg reg = state.getReg reg := by
  rw [final_register]
  simp only [capOpenRecordTailPrefix, capOpenRecordTailInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem cap_open_record_tail_cursor (state : MachineState) :
    (capOpenRecordTailPrefix state 6).getReg .x25 = state.getReg .x25 + 32 := by
  rw [final_register]
  simp (disch := decide) only [capOpenRecordTailPrefix, capOpenRecordTailInstructions,
    List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  rfl

theorem cap_open_record_tail_index (state : MachineState) :
    (capOpenRecordTailPrefix state 6).getReg .x20 =
      state.getReg .x20 + state.getReg .x19 := by
  rw [final_register]
  simp (disch := decide) only [capOpenRecordTailPrefix, capOpenRecordTailInstructions,
    List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]

theorem cap_open_record_tail_count (state : MachineState) :
    (capOpenRecordTailPrefix state 6).getReg .x28 = 17 := by
  rw [final_register]
  exact cap_open_record_tail_counter state

end CommitGolfCandidate
