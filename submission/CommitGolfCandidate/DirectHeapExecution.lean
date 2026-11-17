import CommitGolfCandidate.DirectHeapMemory
import CommitGolfCandidate.StreamingExecution
import CommitGolfCandidate.HoistHelpers
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def heapStreamingFirstState (state : MachineState) (cursor : Nat) : MachineState :=
  (state.setReg .x10 (BitVec.ofNat 64 cursor)).setPC (state.pc + 4)

def heapStreamingArgsState (state : MachineState) (cursor : Nat) : MachineState :=
  ((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
    (state.getReg .x23)).setPC (state.pc + 8)

def heapStreamingReplyState (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) : MachineState :=
  writeBits (heapStreamingArgsState state cursor) (state.getReg .x23) answer

theorem heap_streaming_args_memory (state : MachineState) (cursor : Nat) :
    (heapStreamingArgsState state cursor).mem = state.mem := rfl

theorem heap_streaming_reply_memory (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) :
    (heapStreamingReplyState state cursor answer).mem =
      (writeBits state (state.getReg .x23) answer).mem :=
  write_bits_memory_congr _ _ _ answer rfl

theorem heap_streaming_args_ready (state : MachineState) (cursor : Nat)
    (ready : StreamingOracleReady state) :
    StreamingOracleReady (heapStreamingArgsState state cursor) := by
  rcases ready with ⟨r5, r11, r13⟩
  exact ⟨r5, r11, r13⟩

theorem heap_streaming_oracle_input (state : MachineState) (cursor : Nat)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0) :
    oracleInput (heapStreamingArgsState state cursor) =
      some (.inl (readBuffer state cursor 64)) := by
  have sourceBound : cursor < 2^64 := by
    unfold MEMORY_BYTES at bounded
    omega
  have sourceNat : (BitVec.ofNat 64 cursor).toNat = cursor :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBound]
  have heapBound : (state.getReg .x23).toNat + 32 ≤ MEMORY_BYTES := by
    simpa [rangeValid] using heapValid.1
  have heapAligned := heapValid.2
  rcases heap_streaming_args_ready state cursor ready with ⟨r5, r11, r13⟩
  have r10 : (heapStreamingArgsState state cursor).getReg .x10 =
      BitVec.ofNat 64 cursor := rfl
  have r12 : (heapStreamingArgsState state cursor).getReg .x12 =
      state.getReg .x23 := rfl
  have kind : ((heapStreamingArgsState state cursor).getReg .x13).toNat = 0 := by
    rw [r13]; rfl
  have memory := read_buffer_memory_congr (heapStreamingArgsState state cursor) state rfl cursor 64
  simp [oracleInput, kind, r10, r11, r12, sourceNat,
    COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, aligned,
    heapAligned, heapBound, bounded, memory]
  exact (hoist_read_width (heapStreamingArgsState state cursor) cursor _ kind).trans memory

theorem heap_streaming_machine_block (image : Image) (state : MachineState) (cursor : Nat)
    (inputOffset : BitVec 12)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fetchInput : fetch image state = some (.base (.ADDI .x10 .x8 inputOffset)))
    (stepInput : ordinaryStep state (.base (.ADDI .x10 .x8 inputOffset)) =
      some (heapStreamingFirstState state cursor))
    (fetchOutput : fetch image (heapStreamingFirstState state cursor) =
      some (.base (.ADDI .x12 .x23 0)))
    (stepOutput : ordinaryStep (heapStreamingFirstState state cursor)
      (.base (.ADDI .x12 .x23 0)) = some (heapStreamingArgsState state cursor))
    (fetchCall : fetch image (heapStreamingArgsState state cursor) = some (.base .ECALL))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (heapStreamingReplyState state cursor answer) allowCoins
          return result.charge 10 1) := by
  rw [show 3 + fuel = (fuel + 2) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchInput stepInput,
    execute_ordinary_step _ _ _ _ _ _ fetchOutput stepOutput]
  have r5 : (heapStreamingArgsState state cursor).getReg .x5 = 0 :=
    (heap_streaming_args_ready state cursor ready).1
  rw [execute, fetchCall, if_pos r5,
    heap_streaming_oracle_input state cursor ready aligned bounded heapValid]
  simp only [writeOracleAnswer, oracleCycles, COMPRESSION_CYCLES,
    instructionCycles, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have output : (heapStreamingArgsState state cursor).getReg .x12 =
      state.getReg .x23 := rfl
  simp [output, heapStreamingReplyState, Execution.charge, ← Nat.add_assoc]
  rfl
def heapStreamingMachineBlocks (state : MachineState) (cursor count : Nat) :
    OracleComp World MachineState :=
  match count with
  | 0 => pure state
  | count + 1 => do
      let body ← streamingMachineBlocks state cursor count
      let answer ← World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))
      return heapStreamingReplyState body (cursor + 32 * count) answer

theorem heap_streaming_reply_pc (state : MachineState) (cursor : Nat) (answer : BitVec 256) :
    (heapStreamingReplyState state cursor answer).pc = state.pc + 12 := by
  change state.pc + 8 + 4 = _
  rw [BitVec.add_assoc]
  rfl

theorem heap_streaming_reply_register (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) (reg : Reg) (preserved : reg ∉ [Reg.x10, .x12]) :
    (heapStreamingReplyState state cursor answer).getReg reg = state.getReg reg := by
  rw [heapStreamingReplyState, writeBits_register]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  simp only [heapStreamingArgsState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.2),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.1)]

theorem heap_streaming_machine_registers (state : MachineState) (cursor count : Nat)
    (finished : MachineState)
    (reachable : finished ∈ support (heapStreamingMachineBlocks state cursor count)) :
    finished.pc = state.pc + BitVec.ofNat 64 (12 * count) ∧
    ∀ reg ∉ [Reg.x10, .x12], finished.getReg reg = state.getReg reg := by
  cases count with
  | zero =>
    simp only [heapStreamingMachineBlocks, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count =>
    simp only [heapStreamingMachineBlocks, mem_support_bind_iff] at reachable
    obtain ⟨body, reached, answer, _, finishedEq⟩ := reachable
    change BitVec 256 at answer
    simp only [support_pure, Set.mem_singleton_iff] at finishedEq
    subst finished
    have prior :=  streaming_machine_registers state cursor count body reached
    refine ⟨?_, fun reg preserved =>
      (heap_streaming_reply_register _ _ _ reg preserved).trans (prior.2 reg preserved)⟩
    rw [heap_streaming_reply_pc, prior.1,
      show 12 * (count + 1) = 12 * count + 12 by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

theorem heap_streaming_machine_memory (oracle : Oracle) (left right : MachineState)
    (cursor count : Nat) (same : left.mem = right.mem) :
    (checkEvaluation oracle (heapStreamingMachineBlocks left cursor count)).1.mem =
      (checkEvaluation oracle
        (heapStreamingBlocks right cursor count (left.getReg .x23).toNat)).1.mem ∧
    (checkEvaluation oracle (heapStreamingMachineBlocks left cursor count)).2 =
      (checkEvaluation oracle
        (heapStreamingBlocks right cursor count (left.getReg .x23).toNat)).2 := by
  cases count with
  | zero =>
    simpa [heapStreamingMachineBlocks, heapStreamingBlocks, check_evaluation_pure] using same
  | succ count =>
    let body := (checkEvaluation oracle (streamingMachineBlocks left cursor count)).1
    let reference := (checkEvaluation oracle (streamingBlocks right cursor count)).1
    have prior :=  streaming_machine_memory oracle left right cursor count same
    have registers := streaming_machine_registers left cursor count body
      (check_evaluation_support oracle _)
    have pointer : body.getReg .x23 = left.getReg .x23 := registers.2 .x23 (by simp)
    have input := read_buffer_memory_congr body reference prior.1 (cursor + 32 * count) 64
    rw [heapStreamingMachineBlocks, heapStreamingBlocks, check_evaluation_bind,
      check_evaluation_bind]
    change
      (checkEvaluation oracle
        (do let answer ← World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))
            return heapStreamingReplyState body (cursor + 32 * count) answer)).1.mem = _ ∧ _
    simp only [check_evaluation_public_bind, check_evaluation_pure]
    constructor
    · let answer : BitVec 256 :=
        oracle.compression (readBuffer body (cursor + 32 * count) 64)
      let referenceAnswer : BitVec 256 :=
        oracle.compression (readBuffer reference (cursor + 32 * count) 64)
      have answers : answer = referenceAnswer := congrArg oracle.compression input
      change (heapStreamingReplyState body (cursor + 32 * count) answer).mem =
        (writeBits reference (BitVec.ofNat 64 (left.getReg .x23).toNat) referenceAnswer).mem
      rw [heap_streaming_reply_memory, pointer, answers, BitVec.ofNat_toNat]
      exact write_bits_memory_congr body reference _ referenceAnswer prior.1
    · exact congrArg (· + 1) prior.2

end CommitGolfCandidate
