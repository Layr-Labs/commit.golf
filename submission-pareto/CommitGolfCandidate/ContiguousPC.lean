import CommitGolfCandidate.ContiguousPreparation
import CommitGolfCandidate.ContiguousTail

/-! Relocating a leaf changes only instruction PCs. These continuation lemmas
erase that PC after each complete query sequence without changing its inputs,
writes or arbitrary replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer writeBits

theorem contiguous_next_pc (state : MachineState) (heap : Bool)
    (answer : BitVec 256) (pc : Word) :
    cursorNextState (state.setPC pc) heap answer =
      (cursorNextState state heap answer).setPC (pc + 12) := by
  have output : cursorOutputState (state.setPC pc) heap =
      (cursorOutputState state heap).setPC (pc + 4) := by
    cases state
    rfl
  have reply : cursorReplyState (state.setPC pc) heap answer =
      (cursorReplyState state heap answer).setPC (pc + 4 + 4) := by
    unfold cursorReplyState
    rw [output, hoist_write_bits_pc]
    rfl
  unfold cursorNextState
  rw [reply, ← cursor_set_reg_pc, hoist_pc_pc]
  rfl

theorem contiguous_prefix_pc_bind {α : Type} (state : MachineState)
    (cursor count : Nat) (start boundary : Word)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← cursorPrefix (state.setPC start) cursor count
        continuation (finished.setPC boundary)) =
      (do let finished ← cursorPrefix state cursor count
          continuation (finished.setPC boundary)) := by
  induction count generalizing state cursor start with
  | zero => simp only [cursorPrefix, pure_bind, hoist_pc_pc]
  | succ count ih =>
    simp only [cursorPrefix, bind_assoc]
    have input : readBuffer (state.setPC start) cursor 64 = readBuffer state cursor 64 :=
      read_buffer_memory_congr (state.setPC start) state rfl cursor 64
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [contiguous_next_pc, ih]

theorem contiguous_heap_pc_bind {α : Type} (state : MachineState)
    (cursor : Nat) (start boundary : Word)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← cursorHeapBlocks (state.setPC start) cursor 8
        continuation (finished.setPC boundary)) =
      (do let finished ← cursorHeapBlocks state cursor 8
          continuation (finished.setPC boundary)) := by
  let K : MachineState → OracleComp World α := fun body => do
    let answer ← (liftM (World.query (.inr (.inl
      (readBuffer body (cursor + 32 * 7) 64)))) : OracleComp World (BitVec 256))
    continuation ((cursorNextState body true answer).setPC boundary)
  have insensitive (body : MachineState) (pc : Word) : K (body.setPC pc) = K body := by
    have input : readBuffer (body.setPC pc) (cursor + 32 * 7) 64 =
        readBuffer body (cursor + 32 * 7) 64 := read_buffer_memory_congr (body.setPC pc) body rfl (cursor + 32 * 7) 64
    dsimp only [K]
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer body (cursor + 32 * 7) 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [contiguous_next_pc, hoist_pc_pc]
  have normalized := contiguous_prefix_pc_bind state cursor 7 start 0 K
  simp only [insensitive] at normalized
  simp only [cursorHeapBlocks, bind_assoc, pure_bind]
  exact normalized

end CommitGolfCandidate
