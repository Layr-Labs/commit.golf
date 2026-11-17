import CommitGolfCandidate.UnrolledSalt

/-! The eight compression blocks of an unrolled leaf. The first seven are the
retained carried-input blocks; the last writes the reply to the heap slot
x23+32*slot of the segment base, which is the reference heap pointer. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def unrolledOutputInstruction (slot : Nat) (heap : Bool) : Instr :=
  if heap then .ADDI .x12 .x23 (BitVec.ofNat 12 (32 * slot)) else .ADDI .x12 .x10 32

/-- Exact three-instruction layout of the eight blocks of leaf `slot`. -/
def UnrolledBlocksFetched (image : Image) (slot : Nat) (start : Word) : Prop :=
  ∀ (state : MachineState) (block : Nat), block < 8 →
    (state.pc = start + BitVec.ofNat 64 (12 * block) →
      fetch image state = some (.base (unrolledOutputInstruction slot (block = 7)))) ∧
    (state.pc = start + BitVec.ofNat 64 (12 * block + 4) →
      fetch image state = some (.base .ECALL)) ∧
    (state.pc = start + BitVec.ofNat 64 (12 * block + 8) →
      fetch image state = some (.base (.ADDI .x10 .x10 32)))

theorem unrolled_output_step (slot : Nat) (small : 32 * slot < 2048) (state : MachineState)
    (heap : Bool) :
    ordinaryStep (unrolledShift slot state) (.base (unrolledOutputInstruction slot heap)) =
      some (unrolledShift slot (cursorOutputState state heap)) := by
  cases heap with
  | false =>
    change some (((unrolledShift slot state).setReg .x12
      ((unrolledShift slot state).getReg .x10 + signExtend12 32)).setPC
        ((unrolledShift slot state).pc + 4)) = _
    rw [unrolled_shift_register slot state .x10 (by decide) (by decide),
      show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]
    simp only [cursorOutputState, Bool.false_eq_true, ite_false]
    rw [unrolled_shift_set_pc, unrolled_shift_set_reg slot _ .x12 _ (by decide) (by decide)]
    rfl
  | true =>
    change some (((unrolledShift slot state).setReg .x12
      ((unrolledShift slot state).getReg .x23 + signExtend12 (BitVec.ofNat 12 (32 * slot)))).setPC
        ((unrolledShift slot state).pc + 4)) = _
    rw [unrolled_shift_heap, unrolled_sign_extend _ small, BitVec.sub_add_cancel]
    simp only [cursorOutputState, ite_true]
    rw [unrolled_shift_set_pc, unrolled_shift_set_reg slot _ .x12 _ (by decide) (by decide)]
    rfl

theorem unrolled_advance_step (slot : Nat) (state : MachineState) (heap : Bool)
    (answer : BitVec 256) :
    ordinaryStep (unrolledShift slot (cursorReplyState state heap answer)) (.base (.ADDI .x10 .x10 32)) =
      some (unrolledShift slot (cursorNextState state heap answer)) := by
  change some (((unrolledShift slot (cursorReplyState state heap answer)).setReg .x10
    ((unrolledShift slot (cursorReplyState state heap answer)).getReg .x10 + signExtend12 32)).setPC
      ((unrolledShift slot (cursorReplyState state heap answer)).pc + 4)) = _
  have input : (cursorReplyState state heap answer).getReg .x10 = state.getReg .x10 := by
    rw [cursorReplyState, writeBits_register]
    rfl
  have pcEq : (cursorReplyState state heap answer).pc + 4 = state.pc + 12 := by
    change state.pc + 4 + 4 + 4 = state.pc + 12
    rw [BitVec.add_assoc, BitVec.add_assoc]
    rfl
  rw [unrolled_shift_register slot _ .x10 (by decide) (by decide), input,
    show signExtend12 (32 : BitVec 12) = (32 : Word) by decide, unrolled_shift_pc, pcEq,
    ← unrolled_shift_set_reg slot _ .x10 _ (by decide) (by decide), ← unrolled_shift_set_pc]
  rfl

theorem unrolled_output_cycles (slot : Nat) (heap : Bool) :
    instructionCycles (.base (unrolledOutputInstruction slot heap)) = 1 := by
  cases heap <;> rfl

/-- One shifted output setup, syscall and input advance: three instructions,
ten cycles and one query, for every reply. -/
theorem unrolled_machine_block (image : Image) (slot : Nat) (small : 32 * slot < 2048)
    (state : MachineState) (cursor : Nat) (heap : Bool)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fetchOutput : fetch image (unrolledShift slot state) =
      some (.base (unrolledOutputInstruction slot heap)))
    (fetchCall : fetch image (unrolledShift slot (cursorOutputState state heap)) =
      some (.base .ECALL))
    (fetchAdvance : ∀ answer : BitVec 256,
      fetch image (unrolledShift slot (cursorReplyState state heap answer)) =
        some (.base (.ADDI .x10 .x10 32)))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) (unrolledShift slot state) allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (unrolledShift slot (cursorNextState state heap answer)) allowCoins
          return result.charge 10 1) := by
  rw [show 3 + fuel = (fuel + 2) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchOutput (unrolled_output_step slot small state heap),
    unrolled_output_cycles]
  have r5 : (unrolledShift slot (cursorOutputState state heap)).getReg .x5 = 0 := by
    rw [unrolled_shift_register _ _ .x5 (by decide) (by decide)]
    exact ready.1
  rw [execute, fetchCall, if_pos r5, unrolled_shift_oracle_input,
    cursor_oracle_input state cursor heap pointer ready aligned bounded heapValid]
  simp only [writeOracleAnswer, oracleCycles, COMPRESSION_CYCLES, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  change (do let result ← execute image (fuel + 1)
              (writeBits (unrolledShift slot (cursorOutputState state heap))
                (if heap then state.getReg .x23 else state.getReg .x10 + 32) answer) allowCoins
             return (result.charge 8 1).charge 1 0) = _
  rw [unrolled_shift_write_bits]
  change (do let result ← execute image (fuel + 1)
              (unrolledShift slot (cursorReplyState state heap answer)) allowCoins
             return (result.charge 8 1).charge 1 0) = _
  rw [execute_ordinary_step _ _ _ _ _ _
    (fetchAdvance answer) (unrolled_advance_step slot state heap answer)]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem unrolled_pc_four (start : Word) (n : Nat) :
    start + BitVec.ofNat 64 n + 4 = start + BitVec.ofNat 64 (n + 4) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

theorem unrolled_pc_eight (start : Word) (n : Nat) :
    start + BitVec.ofNat 64 n + 4 + 4 = start + BitVec.ofNat 64 (n + 8) := by
  rw [unrolled_pc_four, unrolled_pc_four]

theorem unrolled_pc_twelve (start : Word) (n : Nat) :
    start + BitVec.ofNat 64 n + 12 = start + BitVec.ofNat 64 (n + 12) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

/-- Prefix blocks on the shifted frame follow the retained reference prefix. -/
theorem unrolled_prefix_execute (image : Image) (slot : Nat) (small : 32 * slot < 2048)
    (start : Word) (fetched : UnrolledBlocksFetched image slot start)
    (state : MachineState) (first cursor count : Nat)
    (blocks : first + count ≤ 7)
    (pc : state.pc = start + BitVec.ofNat 64 (12 * first))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 32 * count + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 * count + fuel) (unrolledShift slot state) allowCoins =
      (do let finished ← cursorPrefix state cursor count
          let result ← execute image fuel (unrolledShift slot finished) allowCoins
          return result.charge (10 * count) count) := by
  induction count generalizing state first cursor with
  | zero => simp [cursorPrefix, Execution.charge]
  | succ count ih =>
    have notLast : (first = 7) = False := by
      apply propext; constructor
      · intro h; omega
      · intro h; exact h.elim
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      unrolled_machine_block image slot small state cursor false pointer ready aligned
        (by omega) heapValid
        (by
          have f := (fetched (unrolledShift slot state) first (by omega)).1
            (by rw [unrolled_shift_pc]; exact pc)
          simpa [notLast] using f)
        ((fetched _ first (by omega)).2.1
          (by
            change state.pc + 4 = _
            rw [pc, unrolled_pc_four]))
        (fun answer => (fetched _ first (by omega)).2.2
          (by
            change state.pc + 4 + 4 = _
            rw [pc, unrolled_pc_eight]))]
    simp only [cursorPrefix, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    have nextPC : (cursorNextState state false answer).pc =
        start + BitVec.ofNat 64 (12 * (first + 1)) := by
      rw [cursor_next_pc, pc, unrolled_pc_twelve]
      congr 2
    have nextPointer : (cursorNextState state false answer).getReg .x10 =
        BitVec.ofNat 64 (cursor + 32) := by
      rw [cursor_next_pointer, pointer]
      exact (BitVec.ofNat_add cursor 32).symm
    have nextHeap : rangeValid ((cursorNextState state false answer).getReg .x23) 32 = true ∧
        ((cursorNextState state false answer).getReg .x23).toNat % 8 = 0 := by
      rw [cursor_next_register state false answer .x23 (by decide)]
      exact heapValid
    rw [ih (cursorNextState state false answer) (first + 1) (cursor + 32)
      (by omega) nextPC nextPointer (cursor_next_ready state false answer ready)
      (by omega) (by omega) nextHeap]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Eight shifted blocks: 24 instructions, 80 cycles and eight queries. -/
theorem unrolled_leaf_blocks (image : Image) (slot : Nat) (small : 32 * slot < 2048)
    (start : Word) (fetched : UnrolledBlocksFetched image slot start)
    (state : MachineState) (cursor : Nat) (pc : state.pc = start)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 288 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (24 + fuel) (unrolledShift slot state) allowCoins =
      (do let finished ← cursorHeapBlocks state cursor 8
          let result ← execute image fuel
            (unrolledShift slot (finished.setPC (start + 96))) allowCoins
          return result.charge 80 8) := by
  rw [show 24 + fuel = 3 * 7 + (3 + fuel) by omega,
    unrolled_prefix_execute image slot small start fetched state 0 cursor 7 (by decide)
      (by rw [pc]; simp) pointer ready aligned (by omega) heapValid]
  simp only [cursorHeapBlocks, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have lastPC : body.pc = start + BitVec.ofNat 64 (12 * 7) := by
    rw [cursor_prefix_pc state cursor 7 body reached, pc]
  have lastPointer := cursor_prefix_pointer state cursor 7 pointer body reached
  have lastHeap : rangeValid (body.getReg .x23) 32 = true ∧
      (body.getReg .x23).toNat % 8 = 0 := by
    rw [cursor_prefix_register state cursor 7 body reached .x23 (by decide)]
    exact heapValid
  rw [unrolled_machine_block image slot small body (cursor + 32 * 7) true lastPointer
    (cursor_prefix_ready state cursor 7 ready body reached) (by omega) (by omega) lastHeap
    (by
      have f := (fetched (unrolledShift slot body) 7 (by decide)).1
        (by rw [unrolled_shift_pc]; exact lastPC)
      simpa using f)
    ((fetched _ 7 (by decide)).2.1
      (by
        change body.pc + 4 = _
        rw [lastPC, unrolled_pc_four]))
    (fun answer => (fetched _ 7 (by decide)).2.2
      (by
        change body.pc + 4 + 4 = _
        rw [lastPC, unrolled_pc_eight]))]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  have returnPC : (cursorNextState body true answer).pc = start + 96 := by
    rw [cursor_next_pc, lastPC, unrolled_pc_twelve]
    rfl
  rw [← returnPC, hoist_pc_self]
  simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
