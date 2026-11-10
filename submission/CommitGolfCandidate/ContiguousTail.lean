import CommitGolfCandidate.ContiguousPrefix

/-! The final carried-cursor query writes directly to heap, advances to the next
salt prefix, then falls through to the fused heap latch. All fetched-image
premises are explicit; no return or message-register update is executed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ContiguousTailFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4572 → fetch image state = some (.base (.ADDI .x12 .x23 0))) ∧
    (state.pc = 4576 → fetch image state = some (.base .ECALL)) ∧
    (state.pc = 4580 → fetch image state = some (.base (.ADDI .x10 .x10 32)))

theorem contiguous_heap_block (image : Image) (fetched : ContiguousTailFetched image)
    (state : MachineState) (cursor : Nat) (pc : state.pc = 4572)
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
    apply (fetched (cursorReplyState state true answer)).2.2
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

/-- Eight physical blocks use 24 instructions, 80 cycles and
eight queries. Fetch premises will be discharged against the delivered image. -/
theorem contiguous_leaf_blocks (image : Image)
    (prefixFetched : ContiguousPrefixFetched image) (tailFetched : ContiguousTailFetched image)
    (state : MachineState) (cursor : Nat) (pc : state.pc = 4488)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 288 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (24 + fuel) state allowCoins =
      (do let finished ← cursorHeapBlocks state cursor 8
          let result ← execute image fuel (finished.setPC 4584) allowCoins
          return result.charge 80 8) := by
  rw [show 24 + fuel = 3 * 7 + (3 + fuel) by omega,
    contiguous_prefix_execute image prefixFetched state 0 cursor 7 (by decide)
      (by simpa using pc) pointer ready aligned (by simpa using bounded) heapValid]
  simp only [cursorHeapBlocks, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have lastPC : body.pc = 4572 := by
    rw [cursor_prefix_pc state cursor 7 body reached, pc]
    rfl
  have lastPointer := cursor_prefix_pointer state cursor 7 pointer body reached
  have lastHeap : rangeValid (body.getReg .x23) 32 = true ∧
      (body.getReg .x23).toNat % 8 = 0 := by
    rw [cursor_prefix_register state cursor 7 body reached .x23 (by decide)]
    exact heapValid
  rw [contiguous_heap_block image tailFetched body (cursor + 32 * 7) lastPC lastPointer
    (cursor_prefix_ready state cursor 7 ready body reached) (by omega) (by omega) lastHeap]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  have returnPC : (cursorNextState body true answer).pc = 4584 := by
    rw [cursor_next_pc, lastPC]
    rfl
  rw [← returnPC, hoist_pc_self]
  simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]


end CommitGolfCandidate
