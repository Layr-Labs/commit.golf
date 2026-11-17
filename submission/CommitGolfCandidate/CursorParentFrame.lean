import CommitGolfCandidate.CursorPositionFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

theorem cursor_base_parent_query (state : MachineState) (messageBase : Word) :
    commitParentQuery (cursorBaseFrame state messageBase) = commitParentQuery state := by
  unfold commitParentQuery pointerParentQuery
  change Sum.inl (readBuffer (cursorBaseFrame state messageBase)
    (state.getReg .x10).toNat 64) = Sum.inl (readBuffer state (state.getReg .x10).toNat 64)
  rw [read_buffer_memory_congr (cursorBaseFrame state messageBase) state rfl
    (state.getReg .x10).toNat 64]

theorem cursor_base_parent_reply (state : MachineState) (messageBase : Word)
    (answer : BitVec 256) :
    commitParentState (cursorBaseFrame state messageBase) answer =
      cursorBaseFrame (commitParentState state answer) messageBase := by
  unfold commitParentState pointerParentState
  change writeBits ((state.setReg .x8 messageBase).setReg .x21 (messageBase - 32))
    (state.getReg .x12) answer = _
  rw [cursor_write_reg, cursor_write_reg]
  rfl

theorem cursor_base_parent_next (state : MachineState) (messageBase : Word) :
    commitParentNextState (cursorBaseFrame state messageBase) =
      cursorBaseFrame (commitParentNextState state) messageBase := by
  cases state
  dsimp [commitParentNextState, pointerParentNextState, pointerParentAdvance,
    cursorBaseFrame, MachineState.setReg, MachineState.getReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem cursor_base_parents_bind {α : Type} (state : MachineState) (remaining : Nat)
    (messageBase : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitParents (cursorBaseFrame state messageBase) remaining
        continuation finished) =
      (do let finished ← commitParents state remaining
          continuation (cursorBaseFrame finished messageBase)) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have input : readBuffer (cursorBaseFrame state messageBase) (state.getReg .x10).toNat 64 =
        readBuffer state (state.getReg .x10).toNat 64 :=
      read_buffer_memory_congr (cursorBaseFrame state messageBase) state rfl
        (state.getReg .x10).toNat 64
    simp only [commitParents, bind_assoc, commitParentQuery, pointerParentQuery]
    change (do let answer ← (liftM (World.query (.inr (.inl
                (readBuffer (cursorBaseFrame state messageBase) (state.getReg .x10).toNat 64)))) :
                OracleComp World (BitVec 256))
               let finished ← commitParents
                 (commitParentNextState (commitParentState (cursorBaseFrame state messageBase) answer))
                 remaining
               continuation finished) = _
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (commitParentQuery state))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [cursor_base_parent_reply, cursor_base_parent_next]
    exact ih _

end CommitGolfCandidate
