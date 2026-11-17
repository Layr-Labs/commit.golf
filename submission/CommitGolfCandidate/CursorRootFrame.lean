import CommitGolfCandidate.CursorParentBoundary
import CommitGolfCandidate.CommitTree

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cursor_base_memory (state : MachineState) (messageBase : Word) :
    (cursorBaseFrame state messageBase).mem = state.mem := rfl

theorem cursor_base_register (state : MachineState) (messageBase : Word) (reg : Reg)
    (preserved : reg ∉ [Reg.x8, .x21]) :
    (cursorBaseFrame state messageBase).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  simp only [cursorBaseFrame,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.2)]

theorem cursor_base_exit (state : MachineState) (messageBase : Word) :
    commitExitState (cursorBaseFrame state messageBase) =
      cursorBaseFrame (commitExitState state) messageBase := by
  cases state
  dsimp [commitExitState, cursorBaseFrame, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem cursor_exit_pc (state : MachineState) (pc : Word) :
    commitExitState (state.setPC pc) = commitExitState state := by
  cases state
  rfl

theorem cursor_base_root_copy (state : MachineState) (messageBase : Word) :
    commitCopyState (cursorBaseFrame state messageBase) 79 =
      cursorBaseFrame (commitCopyState state 79) messageBase := by
  rw [commit_copy_expansion, commit_copy_expansion]
  cases state
  dsimp [cursorBaseFrame, List.foldl, execInstrBr, signExtend12,
    MachineState.setReg, MachineState.getReg, MachineState.getMem,
    MachineState.setMem, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

end CommitGolfCandidate
