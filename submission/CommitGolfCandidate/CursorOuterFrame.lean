import CommitGolfCandidate.CursorReference

/-! The carried cursor follows the same heap-end latch as the reference. Its
original-message frame and erased counter remain explicit at loop boundaries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cursor_initial_frame (state : MachineState) (messageBase : Word)
    (source : state.getReg .x8 = messageBase)
    (chain : state.getReg .x21 = messageBase - 32)
    (pointer : state.getReg .x10 = state.getReg .x21)
    (counter : state.getReg .x20 = 0) :
    cursorLeafFrame state messageBase = state := by
  cases state
  dsimp [cursorLeafFrame, cursorBaseFrame, MachineState.getReg,
    MachineState.setReg] at source chain pointer counter ⊢
  congr 1
  funext reg
  cases reg <;> simp_all

/-- The actual latch advances salt and heap pointers while keeping the cursor
frame. Its branch condition consults only the heap pointer and saved heap end. -/
theorem cursor_latch_frame (state : MachineState) (messageBase : Word) :
    outerPhysicalNextState (cursorNormalize state messageBase 4348) =
      cursorNormalize (commitPositionNextState state) messageBase
        (if BitVec.ult (state.getReg .x23 + 32) (state.getReg .x22)
          then 4280 else 4360) := by
  cases state
  dsimp [outerPhysicalNextState, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    commitPositionNextState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

/-- The fixed caller link and leaf entry PC commute with cursor normalization. -/
theorem cursor_call_frame (state : MachineState) (messageBase : Word) :
    commitLeafCallState (cursorLeafFrame state messageBase) =
      cursorLeafFrame (commitLeafCallState state) messageBase := by
  cases state
  dsimp [commitLeafCallState, cursorLeafFrame, cursorBaseFrame, MachineState.setReg,
    MachineState.getReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

/-- The reference return PC is irrelevant after the next latch has normalized
the boundary PC; it cannot influence registers, branch data or memory. -/
theorem cursor_next_frame_pc (state : MachineState) (messageBase returnPC nextPC : Word) :
    cursorNormalize (commitPositionNextState (state.setPC returnPC)) messageBase nextPC =
      cursorNormalize (commitPositionNextState state) messageBase nextPC := by
  cases state
  rfl

end CommitGolfCandidate
