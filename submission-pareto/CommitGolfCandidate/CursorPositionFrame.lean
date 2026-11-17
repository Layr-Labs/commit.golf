import CommitGolfCandidate.CursorInactive
import CommitGolfCandidate.OuterFrame

/-! Reference leaf states retain virtual message and counter progress. The real
machine keeps the original message registers and carries the next input window
in x10. Salt copying uses that same live window without changing memory effects. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def cursorLeafFrame (state : MachineState) (messageBase : Word) : MachineState :=
  ((cursorBaseFrame state messageBase).setReg .x10 (state.getReg .x21)).setReg .x20 0

def cursorNormalize (state : MachineState) (messageBase pc : Word) : MachineState :=
  (cursorLeafFrame state messageBase).setPC pc

private def cursorSaltOps : List Instr :=
  [.LD .x6 .x18 0, .SD .x10 .x6 0,
   .LD .x6 .x18 8, .SD .x10 .x6 8,
   .LD .x6 .x18 16, .SD .x10 .x6 16,
   .ADDI .x6 .x6 0, .SD .x10 .x0 24]

def cursorSaltCopyState (state : MachineState) : MachineState :=
  cursorSaltOps.foldl execInstrBr state

/-- The live cursor selects exactly the consumed prefix selected by the
reference's virtual x21. All salt loads and stores agree as machine operations. -/
theorem cursor_salt_copy_frame (state : MachineState) (messageBase : Word) :
    cursorSaltCopyState (cursorLeafFrame state messageBase) =
      cursorLeafFrame (commitCopyState state 46) messageBase := by
  rw [commit_copy_expansion]
  cases state
  dsimp [cursorSaltCopyState, cursorSaltOps, cursorLeafFrame, cursorBaseFrame,
    List.foldl, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg,
    MachineState.getMem, MachineState.setMem, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem cursor_frame_register (state : MachineState) (messageBase : Word) (reg : Reg)
    (preserved : reg ∉ [Reg.x8, .x21, .x10, .x20]) :
    (cursorLeafFrame state messageBase).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not8, not21, not10, not20⟩
  simp only [cursorLeafFrame, cursorBaseFrame,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not21),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not20)]

theorem cursor_frame_pointer (state : MachineState) (messageBase : Word) :
    (cursorLeafFrame state messageBase).getReg .x10 = state.getReg .x21 := rfl

theorem cursor_frame_memory (state : MachineState) (messageBase : Word) :
    (cursorLeafFrame state messageBase).mem = state.mem := rfl

theorem cursor_frame_pc (state : MachineState) (messageBase : Word) :
    (cursorLeafFrame state messageBase).pc = state.pc := rfl

end CommitGolfCandidate
