import CommitGolfCandidate.CursorFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

theorem cursor_inactive_args (state : MachineState) (cursor : Nat)
    (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21]) (value : Word) :
    streamingArgsState (state.setReg reg value) cursor =
      (streamingArgsState state cursor).setReg reg value := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inactive
  rcases inactive with rfl | rfl <;> cases state <;>
    dsimp [streamingArgsState, MachineState.setReg, MachineState.setPC] <;>
    congr 1 <;> funext r <;> cases r <;> rfl

theorem cursor_inactive_reply (state : MachineState) (cursor : Nat)
    (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21]) (value : Word)
    (answer : BitVec 256) :
    streamingReplyState (state.setReg reg value) cursor answer =
      (streamingReplyState state cursor answer).setReg reg value := by
  unfold streamingReplyState
  rw [cursor_inactive_args state cursor reg inactive value, cursor_write_reg]

theorem cursor_inactive_prefix_bind {α : Type} (state : MachineState)
    (cursor count : Nat) (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21])
    (value : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← streamingMachineBlocks (state.setReg reg value) cursor count
        continuation finished) =
      (do let finished ← streamingMachineBlocks state cursor count
          continuation (finished.setReg reg value)) := by
  induction count generalizing state cursor with
  | zero => rfl
  | succ count ih =>
    have input : readBuffer (state.setReg reg value) cursor 64 =
        readBuffer state cursor 64 :=
      read_buffer_memory_congr (state.setReg reg value) state (by cases reg <;> rfl) cursor 64
    simp only [streamingMachineBlocks, bind_assoc]
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [cursor_inactive_reply state cursor reg inactive value answer]
    exact ih _ _

theorem cursor_inactive_heap_args (state : MachineState) (cursor : Nat)
    (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21]) (value : Word) :
    heapStreamingArgsState (state.setReg reg value) cursor =
      (heapStreamingArgsState state cursor).setReg reg value := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inactive
  rcases inactive with rfl | rfl <;> cases state <;>
    dsimp [heapStreamingArgsState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC] <;>
    congr 1 <;> funext r <;> cases r <;> rfl

theorem cursor_inactive_heap_reply (state : MachineState) (cursor : Nat)
    (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21]) (value : Word)
    (answer : BitVec 256) :
    heapStreamingReplyState (state.setReg reg value) cursor answer =
      (heapStreamingReplyState state cursor answer).setReg reg value := by
  have heap : (state.setReg reg value).getReg .x23 = state.getReg .x23 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inactive
    rcases inactive with rfl | rfl <;> rfl
  unfold heapStreamingReplyState
  rw [cursor_inactive_heap_args state cursor reg inactive value, heap, cursor_write_reg]

theorem cursor_inactive_heap_bind {α : Type} (state : MachineState)
    (cursor count : Nat) (reg : Reg) (inactive : reg ∈ [Reg.x8, .x21])
    (value : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← heapStreamingMachineBlocks (state.setReg reg value) cursor count
        continuation finished) =
      (do let finished ← heapStreamingMachineBlocks state cursor count
          continuation (finished.setReg reg value)) := by
  cases count with
  | zero => rfl
  | succ count =>
    simp only [heapStreamingMachineBlocks, bind_assoc, pure_bind]
    rw [cursor_inactive_prefix_bind state cursor count reg inactive value]
    apply congrArg (fun tail => streamingMachineBlocks state cursor count >>= tail)
    funext body
    have input : readBuffer (body.setReg reg value) (cursor + 32 * count) 64 =
        readBuffer body (cursor + 32 * count) 64 :=
      read_buffer_memory_congr (body.setReg reg value) body (by cases reg <;> rfl)
        (cursor + 32 * count) 64
    rw [input]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [cursor_inactive_heap_reply body _ reg inactive value answer]

def cursorBaseFrame (state : MachineState) (messageBase : Word) : MachineState :=
  (state.setReg .x8 messageBase).setReg .x21 (messageBase - 32)

theorem cursor_base_heap_bind {α : Type} (state : MachineState) (cursor count : Nat)
    (messageBase : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← heapStreamingMachineBlocks (cursorBaseFrame state messageBase)
          cursor count
        continuation finished) =
      (do let finished ← heapStreamingMachineBlocks state cursor count
          continuation (cursorBaseFrame finished messageBase)) := by
  unfold cursorBaseFrame
  rw [cursor_inactive_heap_bind _ cursor count .x21 (by simp) (messageBase - 32),
    cursor_inactive_heap_bind state cursor count .x8 (by simp) messageBase]

end CommitGolfCandidate
