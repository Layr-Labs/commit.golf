import CommitGolfCandidate.CursorExecution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cursor_write_reg {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (reg : Reg) (value : Word) :
    writeBits (state.setReg reg value) address answer =
      (writeBits state address answer).setReg reg value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg reg value).setByte a b = (s.setByte a b).setReg reg value := by
    cases reg <;> cases s <;> rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg reg value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg reg value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons, byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  cases reg <;> rfl

theorem cursor_set_reg_pc (state : MachineState) (reg : Reg) (value pc : Word) :
    (state.setReg reg value).setPC pc = (state.setPC pc).setReg reg value := by
  cases reg <;> cases state <;> rfl

theorem cursor_next_streaming (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) :
    cursorNextState (state.setReg .x10 (BitVec.ofNat 64 cursor)) false answer =
      (streamingReplyState state cursor answer).setReg .x10
        (BitVec.ofNat 64 (cursor + 32)) := by
  have source : (state.setReg .x10 (BitVec.ofNat 64 cursor)).getReg .x10 =
      BitVec.ofNat 64 cursor := rfl
  have output : cursorOutputState (state.setReg .x10 (BitVec.ofNat 64 cursor)) false =
      ((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
        (BitVec.ofNat 64 (cursor + 32))).setPC (state.pc + 4) := by
    simp [cursorOutputState, source, ← BitVec.ofNat_add]
  unfold cursorNextState cursorReplyState
  rw [output]
  simp only [Bool.false_eq_true, ite_false, source]
  have advance : BitVec.ofNat 64 cursor + 32 = BitVec.ofNat 64 (cursor + 32) :=
    (BitVec.ofNat_add cursor 32).symm
  rw [advance, hoist_write_bits_pc]
  unfold streamingReplyState streamingArgsState
  rw [hoist_write_bits_pc, cursor_set_reg_pc]
  simp only [MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
    MachineState.getReg_setPC, MachineState.setPC]
  rw [show state.pc + 8 + 4 = state.pc + 12 by
    rw [BitVec.add_assoc]; rfl]
  rfl

theorem cursor_next_heap (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) :
    cursorNextState (state.setReg .x10 (BitVec.ofNat 64 cursor)) true answer =
      (heapStreamingReplyState state cursor answer).setReg .x10
        (BitVec.ofNat 64 (cursor + 32)) := by
  have source : (state.setReg .x10 (BitVec.ofNat 64 cursor)).getReg .x10 =
      BitVec.ofNat 64 cursor := rfl
  have heap : (state.setReg .x10 (BitVec.ofNat 64 cursor)).getReg .x23 =
      state.getReg .x23 := rfl
  unfold cursorNextState cursorReplyState cursorOutputState
  simp only [ite_true, heap, source]
  have advance : BitVec.ofNat 64 cursor + 32 = BitVec.ofNat 64 (cursor + 32) :=
    (BitVec.ofNat_add cursor 32).symm
  rw [advance, hoist_write_bits_pc]
  unfold heapStreamingReplyState heapStreamingArgsState
  rw [hoist_write_bits_pc, cursor_set_reg_pc]
  simp only [MachineState.getReg_setPC, MachineState.setPC]
  rw [show state.pc + 8 + 4 = state.pc + 12 by
    rw [BitVec.add_assoc]; rfl]
  rfl

theorem cursor_prefix_bind {α : Type} (state : MachineState) (cursor count : Nat)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← cursorPrefix (state.setReg .x10 (BitVec.ofNat 64 cursor)) cursor count
        continuation finished) =
      (do let finished ← streamingMachineBlocks state cursor count
          continuation (finished.setReg .x10 (BitVec.ofNat 64 (cursor + 32 * count)))) := by
  induction count generalizing state cursor with
  | zero => simp [cursorPrefix, streamingMachineBlocks]
  | succ count ih =>
    have input : readBuffer (state.setReg .x10 (BitVec.ofNat 64 cursor)) cursor 64 =
        readBuffer state cursor 64 :=
      read_buffer_memory_congr _ _ rfl _ _
    simp only [cursorPrefix, streamingMachineBlocks, bind_assoc, input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [cursor_next_streaming, ih]
    have nextCursor : cursor + 32 + 32 * count = cursor + 32 * (count + 1) := by omega
    simp only [nextCursor]

theorem cursor_heap_bind {α : Type} (state : MachineState) (cursor count : Nat)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← cursorHeapBlocks (state.setReg .x10 (BitVec.ofNat 64 cursor))
          cursor count
        continuation finished) =
      (do let finished ← heapStreamingMachineBlocks state cursor count
          continuation (finished.setReg .x10 (BitVec.ofNat 64 (cursor + 32 * count)))) := by
  cases count with
  | zero => simp [cursorHeapBlocks, heapStreamingMachineBlocks]
  | succ count =>
    simp only [cursorHeapBlocks, heapStreamingMachineBlocks, bind_assoc, pure_bind]
    rw [cursor_prefix_bind]
    apply congrArg (fun tail => streamingMachineBlocks state cursor count >>= tail)
    funext body
    have input : readBuffer (body.setReg .x10 (BitVec.ofNat 64 (cursor + 32 * count)))
        (cursor + 32 * count) 64 = readBuffer body (cursor + 32 * count) 64 :=
      read_buffer_memory_congr _ _ rfl _ _
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [cursor_next_heap]
    have nextCursor : cursor + 32 * count + 32 = cursor + 32 * (count + 1) := by omega
    simp only [nextCursor]

end CommitGolfCandidate
