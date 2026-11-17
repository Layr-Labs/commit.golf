import CommitGolfCandidate.CursorSupport

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def CursorTailFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4540 → fetch image state = some (.base (.ADDI .x12 .x23 0))) ∧
    (state.pc = 4544 → fetch image state = some (.base .ECALL)) ∧
    (state.pc = 4548 → fetch image state = some (.base (.ADDI .x10 .x10 32))) ∧
    (state.pc = 4552 → fetch image state = some (.base (.JALR .x0 .x1 32)))

theorem cursor_heap_block (image : Image) (fetched : CursorTailFetched image)
    (state : MachineState) (cursor : Nat) (pc : state.pc = 4540)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (cursorNextState state true answer) allowCoins
          return result.charge 10 1) := by
  apply cursor_machine_block image state cursor true pointer ready aligned bounded heapValid
  · exact (fetched state).1 pc
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      cursorOutputState, signExtend12]
  · apply (fetched (cursorOutputState state true)).2.1
    change state.pc + 4 = _
    rw [pc]
    rfl
  · intro answer
    apply (fetched (cursorReplyState state true answer)).2.2.1
    change state.pc + 4 + 4 = _
    rw [pc]
    rfl
  · intro answer
    have input : (cursorReplyState state true answer).getReg .x10 =
        state.getReg .x10 := by
      rw [cursorReplyState, writeBits_register]
      rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      input]
    change some (((cursorReplyState state true answer).setReg .x10
      (state.getReg .x10 + signExtend12 32)).setPC (state.pc + 4 + 4 + 4)) =
      some (cursorNextState state true answer)
    simp [signExtend12, cursorNextState, BitVec.add_assoc]

theorem cursor_return (image : Image) (fetched : CursorTailFetched image)
    (state : MachineState) (pc : state.pc = 4552) (link : state.getReg .x1 = 4316)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let result ← execute image fuel (state.setPC 4348) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 32)) =
      some (state.setPC 4348) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ ((fetched state).2.2.2 pc) stepped]
  rfl

theorem cursor_leaf_subroutine (image : Image)
    (prefixFetched : CursorPrefixFetched image) (tailFetched : CursorTailFetched image)
    (state : MachineState) (cursor : Nat) (pc : state.pc = 4456)
    (link : state.getReg .x1 = 4316)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 288 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (25 + fuel) state allowCoins =
      (do let finished ← cursorHeapBlocks state cursor 8
          let result ← execute image fuel (finished.setPC 4348) allowCoins
          return result.charge 81 8) := by
  rw [show 25 + fuel = 3 * 7 + (3 + (1 + fuel)) by omega,
    cursor_prefix_execute image prefixFetched state 0 cursor 7 (by decide)
      (by simpa using pc) pointer ready aligned (by simpa using bounded) heapValid]
  simp only [cursorHeapBlocks, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have lastPC : body.pc = 4540 := by
    rw [cursor_prefix_pc state cursor 7 body reached, pc]
    rfl
  have lastPointer := cursor_prefix_pointer state cursor 7 pointer body reached
  have lastHeap : rangeValid (body.getReg .x23) 32 = true ∧
      (body.getReg .x23).toNat % 8 = 0 := by
    rw [cursor_prefix_register state cursor 7 body reached .x23 (by decide)]
    exact heapValid
  rw [cursor_heap_block image tailFetched body (cursor + 32 * 7) lastPC lastPointer
    (cursor_prefix_ready state cursor 7 ready body reached) (by omega) (by omega) lastHeap]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  have returnPC : (cursorNextState body true answer).pc = 4552 := by
    rw [cursor_next_pc, lastPC]
    rfl
  have returnLink : (cursorNextState body true answer).getReg .x1 = 4316 :=
    (cursor_next_register body true answer .x1 (by decide)).trans
      ((cursor_prefix_register state cursor 7 body reached .x1 (by decide)).trans link)
  rw [cursor_return image tailFetched _ returnPC returnLink]
  simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
