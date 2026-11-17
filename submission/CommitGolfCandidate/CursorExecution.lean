import CommitGolfCandidate.DirectHeapExecution

/-! Interpreter bridge for a carried compression-input cursor. The input pointer
is already live in x10. An output-address instruction precedes the syscall, and
one cursor increment follows its arbitrary reply. The syscall snapshots the
input before its potentially overlapping write. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def cursorOutputState (state : MachineState) (heap : Bool) : MachineState :=
  (state.setReg .x12 (if heap then state.getReg .x23 else state.getReg .x10 + 32)).setPC
    (state.pc + 4)

def cursorReplyState (state : MachineState) (heap : Bool)
    (answer : BitVec 256) : MachineState :=
  writeBits (cursorOutputState state heap)
    (if heap then state.getReg .x23 else state.getReg .x10 + 32) answer

def cursorNextState (state : MachineState) (heap : Bool)
    (answer : BitVec 256) : MachineState :=
  ((cursorReplyState state heap answer).setReg .x10 (state.getReg .x10 + 32)).setPC
    (state.pc + 12)

/-- The carried pointer and fixed selector registers establish the same real
range-checked syscall as the existing streaming bridge. -/
theorem cursor_oracle_input (state : MachineState) (cursor : Nat) (heap : Bool)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0) :
    oracleInput (cursorOutputState state heap) =
      some (.inl (readBuffer state cursor 64)) := by
  have bound : cursor < 2^64 := by unfold MEMORY_BYTES at bounded; omega
  have destinationBound : cursor + 32 < 2^64 := by
    unfold MEMORY_BYTES at bounded; omega
  have sourceNat : (BitVec.ofNat 64 cursor).toNat = cursor := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  have destinationNat : (BitVec.ofNat 64 (cursor + 32)).toNat = cursor + 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
  rcases ready with ⟨r5, r11, r13⟩
  have kind : ((cursorOutputState state heap).getReg .x13).toNat = 0 := by
    change (state.getReg .x13).toNat = 0
    rw [r13]; rfl
  have memory : readBuffer (cursorOutputState state heap) cursor 64 =
      readBuffer state cursor 64 :=
    read_buffer_memory_congr _ _ rfl _ _
  have r10 : (cursorOutputState state heap).getReg .x10 = BitVec.ofNat 64 cursor :=
    pointer
  have widthReg : (cursorOutputState state heap).getReg .x11 = 64 := r11
  have width := hoist_read_width (cursorOutputState state heap) cursor _ kind
  cases heap with
  | false =>
    have output : (cursorOutputState state false).getReg .x12 =
        BitVec.ofNat 64 (cursor + 32) := by
      change state.getReg .x10 + 32 = _
      rw [pointer]
      exact (BitVec.ofNat_add cursor 32).symm
    simp [oracleInput, kind, r10, widthReg, output, sourceNat, destinationNat,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, aligned,
      bounded, show (cursor + 32) % 8 = 0 by omega,
      show cursor + 32 + 32 ≤ MEMORY_BYTES by omega, memory]
    exact width.trans memory
  | true =>
    have output : (cursorOutputState state true).getReg .x12 =
        state.getReg .x23 := rfl
    have heapBound : (state.getReg .x23).toNat + 32 ≤ MEMORY_BYTES := by
      simpa [rangeValid] using heapValid.1
    simp [oracleInput, kind, r10, widthReg, output, sourceNat,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid,
      aligned, bounded, heapValid.2, heapBound, memory]
    exact width.trans memory

/-- The output setup, eight-cycle syscall and input-pointer increment cost
three instructions and ten cycles, with one query for every possible reply. -/
theorem cursor_machine_block (image : Image) (state : MachineState)
    (cursor : Nat) (heap : Bool)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fetchOutput : fetch image state =
      some (.base (.ADDI .x12 (if heap then .x23 else .x10) (if heap then 0 else 32))))
    (stepOutput : ordinaryStep state
      (.base (.ADDI .x12 (if heap then .x23 else .x10) (if heap then 0 else 32))) =
      some (cursorOutputState state heap))
    (fetchCall : fetch image (cursorOutputState state heap) = some (.base .ECALL))
    (fetchAdvance : ∀ answer : BitVec 256,
      fetch image (cursorReplyState state heap answer) =
        some (.base (.ADDI .x10 .x10 32)))
    (stepAdvance : ∀ answer : BitVec 256,
      ordinaryStep (cursorReplyState state heap answer) (.base (.ADDI .x10 .x10 32)) =
        some (cursorNextState state heap answer))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (cursorNextState state heap answer) allowCoins
          return result.charge 10 1) := by
  rw [show 3 + fuel = (fuel + 2) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchOutput stepOutput]
  have r5 : (cursorOutputState state heap).getReg .x5 = 0 := ready.1
  rw [execute, fetchCall, if_pos r5,
    cursor_oracle_input state cursor heap pointer ready aligned bounded heapValid]
  simp only [writeOracleAnswer, oracleCycles, COMPRESSION_CYCLES,
    instructionCycles, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have output : (cursorOutputState state heap).getReg .x12 =
      if heap then state.getReg .x23 else state.getReg .x10 + 32 := rfl
  rw [output]
  change (do let result ← execute image (fuel + 1)
              (cursorReplyState state heap answer) allowCoins
             return (result.charge 8 1).charge 1 0) = _
  rw [execute_ordinary_step _ _ _ _ _ _
    (fetchAdvance answer) (stepAdvance answer)]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

/-- Prefix semantics parameterize the same input windows explicitly. The
machine bridge separately establishes that the live x10 equals each window. -/
def cursorPrefix : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, cursor, count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
      cursorPrefix (cursorNextState state false answer) (cursor + 32) count

def cursorHeapBlocks (state : MachineState) (cursor count : Nat) :
    OracleComp World MachineState :=
  match count with
  | 0 => pure state
  | count + 1 => do
      let body ← cursorPrefix state cursor count
      let answer ← World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))
      return cursorNextState body true answer

end CommitGolfCandidate
