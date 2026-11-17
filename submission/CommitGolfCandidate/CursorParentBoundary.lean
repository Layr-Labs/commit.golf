import CommitGolfCandidate.CursorParentFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] BitVec.shiftLeft

private def cursorParentPrefix (state : MachineState) : MachineState :=
  ([.ADDI .x20 .x19 4095, .SLLI .x6 .x20 6,
    .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5] : List Instr).foldl execInstrBr state

private def cursorParentBranch (state : MachineState) : MachineState :=
  (cursorParentPrefix state).setPC
    (if state.getReg .x19 - 1 = 0 then 4412 else 4384)

theorem cursor_base_pc (state : MachineState) (messageBase pc : Word) :
    (cursorBaseFrame state messageBase).setPC pc =
      cursorBaseFrame (state.setPC pc) messageBase := by
  cases state
  rfl

private def cursorInputFrame (state : MachineState) (messageBase input : Word) : MachineState :=
  (cursorBaseFrame state messageBase).setReg .x10 input

private theorem cursor_parent_first (state : MachineState) (messageBase pc : Word) :
    execInstrBr (cursorNormalize state messageBase pc) (.ADDI .x20 .x19 4095) =
      cursorInputFrame (execInstrBr (state.setPC pc) (.ADDI .x20 .x19 4095))
        messageBase (state.getReg .x21) := by
  cases state
  dsimp [cursorNormalize, cursorLeafFrame, cursorBaseFrame, cursorInputFrame,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  generalize signExtend12 (4095 : BitVec 12) = immediate
  congr 1
  funext reg
  cases reg <;> simp

private theorem cursor_parent_shift (state : MachineState) (messageBase input : Word) :
    execInstrBr (cursorInputFrame state messageBase input) (.SLLI .x6 .x20 6) =
      cursorInputFrame (execInstrBr state (.SLLI .x6 .x20 6)) messageBase input := by
  cases state
  dsimp [cursorInputFrame, cursorBaseFrame, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> simp

private theorem cursor_parent_address (state : MachineState) (messageBase input : Word) :
    execInstrBr (cursorInputFrame state messageBase input) (.ADD .x10 .x9 .x6) =
      cursorBaseFrame (execInstrBr state (.ADD .x10 .x9 .x6)) messageBase := by
  cases state
  dsimp [cursorInputFrame, cursorBaseFrame, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> simp

private theorem cursor_parent_final_shift (state : MachineState) (messageBase : Word) :
    execInstrBr (cursorBaseFrame state messageBase) (.SLLI .x7 .x20 5) =
      cursorBaseFrame (execInstrBr state (.SLLI .x7 .x20 5)) messageBase := by
  cases state
  dsimp [cursorBaseFrame, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> simp

private theorem cursor_parent_prefix_boundary (state : MachineState) (messageBase pc : Word) :
    cursorParentPrefix (cursorNormalize state messageBase pc) =
      cursorBaseFrame (cursorParentPrefix (state.setPC pc)) messageBase := by
  unfold cursorParentPrefix
  simp only [List.foldl]
  rw [cursor_parent_first, cursor_parent_shift, cursor_parent_address,
    cursor_parent_final_shift]

private theorem cursor_parent_branch_boundary (state : MachineState) (messageBase pc : Word) :
    cursorParentBranch (cursorNormalize state messageBase pc) =
      cursorBaseFrame (cursorParentBranch (state.setPC pc)) messageBase := by
  unfold cursorParentBranch
  change (cursorParentPrefix (cursorNormalize state messageBase pc)).setPC
    (if state.getReg .x19 - 1 = 0 then 4412 else 4384) = _
  rw [cursor_parent_prefix_boundary, cursor_base_pc]
  rfl

private theorem cursor_parent_last_add (state : MachineState) (messageBase : Word) :
    execInstrBr (cursorBaseFrame state messageBase) (.ADD .x12 .x9 .x7) =
      cursorBaseFrame (execInstrBr state (.ADD .x12 .x9 .x7)) messageBase := by
  cases state
  dsimp [cursorBaseFrame, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> simp

theorem cursor_parent_boundary (state : MachineState) (messageBase pc : Word) :
    commitParentsStartState (cursorNormalize state messageBase pc) =
      cursorBaseFrame (commitParentsStartState (state.setPC pc)) messageBase := by
  change (if state.getReg .x19 - 1 = 0
      then cursorParentBranch (cursorNormalize state messageBase pc)
      else execInstrBr (cursorParentBranch (cursorNormalize state messageBase pc)) (.ADD .x12 .x9 .x7)) =
    cursorBaseFrame (if state.getReg .x19 - 1 = 0
      then cursorParentBranch (state.setPC pc)
      else execInstrBr (cursorParentBranch (state.setPC pc)) (.ADD .x12 .x9 .x7)) messageBase
  rw [cursor_parent_branch_boundary]
  split <;> simp only [cursor_parent_last_add]

end CommitGolfCandidate
