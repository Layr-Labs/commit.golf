import CommitGolfCandidate.StreamingMemory
import CommitGolfCandidate.HoistHelpers
import CommitGolfCandidate.CopyRefinement

/-! Exact interpreter bridge for one streaming compression. Fetch and ordinary
step premises identify the image's two address instructions. The syscall checks
the real memory limits; its read precedes the destructive output write. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Only the selector, input width, and primitive remain fixed across blocks. -/
def StreamingOracleReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0

def streamingFirstState (state : MachineState) (cursor : Nat) : MachineState :=
  (state.setReg .x10 (BitVec.ofNat 64 cursor)).setPC (state.pc + 4)

def streamingArgsState (state : MachineState) (cursor : Nat) : MachineState :=
  ((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
    (BitVec.ofNat 64 (cursor + 32))).setPC (state.pc + 8)

def streamingReplyState (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) : MachineState :=
  writeBits (streamingArgsState state cursor) (BitVec.ofNat 64 (cursor + 32)) answer

theorem streaming_args_memory (state : MachineState) (cursor : Nat) :
    (streamingArgsState state cursor).mem = state.mem := rfl

theorem streaming_reply_memory (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) :
    (streamingReplyState state cursor answer).mem =
      (writeBits state (BitVec.ofNat 64 (cursor + 32)) answer).mem :=
  write_bits_memory_congr _ _ _ answer rfl

theorem streaming_args_ready (state : MachineState) (cursor : Nat)
    (ready : StreamingOracleReady state) :
    StreamingOracleReady (streamingArgsState state cursor) := by
  rcases ready with ⟨r5, r11, r13⟩
  exact ⟨r5, r11, r13⟩

/-- Real `oracleInput` accepts the moving 64-byte chain/block window and a
32-byte reply within it, with the exact unchanged input bytes. -/
theorem streaming_oracle_input (state : MachineState) (cursor : Nat)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES) :
    oracleInput (streamingArgsState state cursor) =
      some (.inl (readBuffer state cursor 64)) := by
  have sourceBound : cursor < 2^64 := by
    unfold MEMORY_BYTES at bounded
    omega
  have destinationBound : cursor + 32 < 2^64 := by
    unfold MEMORY_BYTES at bounded
    omega
  have sourceNat : (BitVec.ofNat 64 cursor).toNat = cursor :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sourceBound]
  have destinationNat : (BitVec.ofNat 64 (cursor + 32)).toNat = cursor + 32 :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt destinationBound]
  rcases streaming_args_ready state cursor ready with ⟨r5, r11, r13⟩
  have r10 : (streamingArgsState state cursor).getReg .x10 =
      BitVec.ofNat 64 cursor := rfl
  have r12 : (streamingArgsState state cursor).getReg .x12 =
      BitVec.ofNat 64 (cursor + 32) := rfl
  have kind : ((streamingArgsState state cursor).getReg .x13).toNat = 0 := by
    rw [r13]; rfl
  have memory := read_buffer_memory_congr (streamingArgsState state cursor) state rfl cursor 64
  simp [oracleInput, kind, r10, r11, r12, sourceNat, destinationNat,
    COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, aligned,
    show (cursor + 32) % 8 = 0 by omega,
    show cursor + 32 + 32 ≤ MEMORY_BYTES by omega, bounded, memory]
  exact (hoist_read_width (streamingArgsState state cursor) cursor _ kind).trans memory

/-- Two single-cycle address instructions and one eight-cycle ECALL: exactly
three instructions, ten cycles, one query, and an arbitrary 256-bit reply. -/
theorem streaming_machine_block (image : Image) (state : MachineState) (cursor : Nat)
    (inputOffset outputOffset : BitVec 12)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (fetchInput : fetch image state = some (.base (.ADDI .x10 .x8 inputOffset)))
    (stepInput : ordinaryStep state (.base (.ADDI .x10 .x8 inputOffset)) =
      some (streamingFirstState state cursor))
    (fetchOutput : fetch image (streamingFirstState state cursor) =
      some (.base (.ADDI .x12 .x8 outputOffset)))
    (stepOutput : ordinaryStep (streamingFirstState state cursor)
      (.base (.ADDI .x12 .x8 outputOffset)) = some (streamingArgsState state cursor))
    (fetchCall : fetch image (streamingArgsState state cursor) = some (.base .ECALL))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (streamingReplyState state cursor answer) allowCoins
          return result.charge 10 1) := by
  rw [show 3 + fuel = (fuel + 2) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchInput stepInput,
    execute_ordinary_step _ _ _ _ _ _ fetchOutput stepOutput]
  have r5 : (streamingArgsState state cursor).getReg .x5 = 0 :=
    (streaming_args_ready state cursor ready).1
  rw [execute, fetchCall, if_pos r5,
    streaming_oracle_input state cursor ready aligned bounded]
  simp only [writeOracleAnswer, oracleCycles, COMPRESSION_CYCLES,
    instructionCycles, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have output : (streamingArgsState state cursor).getReg .x12 =
      BitVec.ofNat 64 (cursor + 32) := rfl
  simp [output, streamingReplyState, Execution.charge, ← Nat.add_assoc]
  rfl

/-- Reference state distribution for the real two-address-instruction blocks. -/
def streamingMachineBlocks : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, cursor, count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
      streamingMachineBlocks (streamingReplyState state cursor answer) (cursor + 32) count

theorem streaming_reply_pc (state : MachineState) (cursor : Nat) (answer : BitVec 256) :
    (streamingReplyState state cursor answer).pc = state.pc + 12 := by
  change state.pc + 8 + 4 = _
  rw [BitVec.add_assoc]
  rfl

theorem streaming_reply_register (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) (reg : Reg) (preserved : reg ∉ [Reg.x10, .x12]) :
    (streamingReplyState state cursor answer).getReg reg = state.getReg reg := by
  rw [streamingReplyState, writeBits_register]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  simp only [streamingArgsState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.2),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm preserved.1)]

/-- The two addresses are overwritten before every query. Every other register,
including the live selectors, source base, chain pointer, and link, is preserved. -/
theorem streaming_machine_registers (state : MachineState) (cursor count : Nat)
    (finished : MachineState)
    (reachable : finished ∈ support (streamingMachineBlocks state cursor count)) :
    finished.pc = state.pc + BitVec.ofNat 64 (12 * count) ∧
    ∀ reg ∉ [Reg.x10, .x12], finished.getReg reg = state.getReg reg := by
  induction count generalizing state cursor with
  | zero =>
    simp only [streamingMachineBlocks, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [streamingMachineBlocks, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have rest := ih _ _ reached
    refine ⟨?_, fun reg preserved =>
      (rest.2 reg preserved).trans (streaming_reply_register _ _ _ reg preserved)⟩
    rw [rest.1, streaming_reply_pc,
      show 12 * (count + 1) = 12 + 12 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rfl

/-- Register setup changes no memory, so machine block evaluation has exactly
the byte effects and query count of the reference streaming computation. -/
theorem streaming_machine_memory (oracle : Oracle) (left right : MachineState)
    (cursor count : Nat) (same : left.mem = right.mem) :
    (checkEvaluation oracle (streamingMachineBlocks left cursor count)).1.mem =
      (checkEvaluation oracle (streamingBlocks right cursor count)).1.mem ∧
    (checkEvaluation oracle (streamingMachineBlocks left cursor count)).2 =
      (checkEvaluation oracle (streamingBlocks right cursor count)).2 := by
  induction count generalizing left right cursor with
  | zero => simpa [streamingMachineBlocks, streamingBlocks, check_evaluation_pure] using same
  | succ count ih =>
    have input := read_buffer_memory_congr left right same cursor 64
    rw [streamingMachineBlocks, streamingBlocks, check_evaluation_public_bind,
      check_evaluation_public_bind, input]
    have next := ih
      (streamingReplyState left cursor (oracle.compression (readBuffer right cursor 64)))
      (writeBits right (BitVec.ofNat 64 (cursor + 32))
        (oracle.compression (readBuffer right cursor 64)))
      (cursor + 32)
      ((streaming_reply_memory _ _ _).trans (write_bits_memory_congr _ _ _ _ same))
    exact ⟨next.1, congrArg (1 + ·) next.2⟩

end CommitGolfCandidate
