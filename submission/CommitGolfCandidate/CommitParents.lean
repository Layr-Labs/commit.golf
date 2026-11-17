import CommitGolfCandidate.PointerParents

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery := pointerParentQuery
abbrev commitParentState := pointerParentState
abbrev commitParentNextState := pointerParentNextState

theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x12) answer).mem := rfl

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc = state.pc + 4 := by
  simp [pointerParentState, writeBits, MachineState.setPC]

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (commitParentState state answer).getReg reg = state.getReg reg :=
  pointer_parent_register state answer reg

theorem commit_parent_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x20, .x21, .x26, .x5, .x11, .x13]) :
    (commitParentNextState (commitParentState state answer)).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_input (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x10 =
      state.getReg .x10 - 64 := by
  simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_output (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x12 =
      state.getReg .x12 - 32 := by
  simp [pointerParentNextState, pointerParentAdvance, pointer_parent_register,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

theorem commit_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).pc =
      if state.getReg .x12 - 32 = state.getReg .x9 then 4404 else 4388 := by
  simp [pointerParentNextState, pointer_parent_register, MachineState.setPC]

end CommitGolfCandidate
