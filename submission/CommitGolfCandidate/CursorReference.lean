import CommitGolfCandidate.CursorPositionFrame
import CommitGolfCandidate.CursorTail

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

theorem cursor_frame_reorder (state : MachineState) (messageBase : Word) :
    cursorLeafFrame state messageBase =
      ((cursorBaseFrame state messageBase).setReg .x20 0).setReg .x10
        (state.getReg .x21) := by
  cases state
  dsimp [cursorLeafFrame, cursorBaseFrame, MachineState.setReg, MachineState.getReg]
  congr 1
  funext reg
  cases reg <;> rfl

theorem cursor_finished_frame (body : MachineState) (cursor : Nat)
    (source : body.getReg .x8 = BitVec.ofNat 64 (cursor + 32))
    (messageBase : Word) :
    cursorNormalize (commitLeafFinishState body 8) messageBase 4348 =
      (((cursorBaseFrame body messageBase).setReg .x20 0).setReg .x10
        (BitVec.ofNat 64 (cursor + 256))).setPC 4348 := by
  have advance : (commitLeafFinishState body 8).getReg .x21 =
      BitVec.ofNat 64 (cursor + 256) := by
    change body.getReg .x8 + BitVec.ofNat 64 256 - 32 = _
    rw [source, ← BitVec.ofNat_add]
    rw [show cursor + 32 + 256 = (cursor + 256) + 32 by omega,
      BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  unfold cursorNormalize cursorLeafFrame
  rw [advance]
  cases body
  dsimp [cursorBaseFrame, commitLeafFinishState, MachineState.setReg,
    MachineState.getReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem cursor_leaf_reference_bind {α : Type} (state : MachineState) (cursor : Nat)
    (source : state.getReg .x8 = BitVec.ofNat 64 (cursor + 32))
    (chain : state.getReg .x21 = BitVec.ofNat 64 cursor)
    (window : (state.getReg .x8).toNat - 32 = cursor)
    (messageBase : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← cursorHeapBlocks (cursorLeafFrame state messageBase) cursor 8
        continuation (finished.setPC 4348)) =
      (do let finished ← commitLeafLoop state 8
          continuation (cursorNormalize finished messageBase 4348)) := by
  rw [cursor_frame_reorder, chain, cursor_heap_bind,
    outer_heap_bind (cursorBaseFrame state messageBase) cursor 8 0,
    cursor_base_heap_bind state cursor 8 messageBase]
  simp only [commitLeafLoop, bind_assoc, pure_bind, window]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have bodySource : body.getReg .x8 = BitVec.ofNat 64 (cursor + 32) :=
    ((heap_streaming_machine_registers state cursor 8 body reached).2 .x8 (by decide)).trans source
  rw [cursor_finished_frame body cursor bodySource messageBase]

end CommitGolfCandidate
