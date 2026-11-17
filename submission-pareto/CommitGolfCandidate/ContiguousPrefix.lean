import CommitGolfCandidate.CursorSupport

/-! The contiguous salt/hash body relocates the unchanged seven prefix triplets
by 32 bytes. This bridge retains actual bounds and arbitrary-reply execution. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact three-instruction layout of each ordinary prefix block. -/
def ContiguousPrefixFetched (image : Image) : Prop :=
  ∀ (state : MachineState) (block : Nat), block < 7 →
    (state.pc = BitVec.ofNat 64 (4484 + 12 * block) →
      fetch image state = some (.base (.ADDI .x12 .x10 32))) ∧
    (state.pc = BitVec.ofNat 64 (4488 + 12 * block) →
      fetch image state = some (.base .ECALL)) ∧
    (state.pc = BitVec.ofNat 64 (4492 + 12 * block) →
      fetch image state = some (.base (.ADDI .x10 .x10 32)))

theorem contiguous_prefix_block (image : Image) (fetched : ContiguousPrefixFetched image)
    (state : MachineState) (block cursor : Nat) (blockBound : block < 7)
    (pc : state.pc = BitVec.ofNat 64 (4484 + 12 * block))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (cursorNextState state false answer) allowCoins
          return result.charge 10 1) := by
  apply cursor_machine_block image state cursor false pointer ready aligned bounded heapValid
  · exact (fetched state block blockBound).1 pc
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      cursorOutputState, signExtend12]
  · apply (fetched (cursorOutputState state false) block blockBound).2.1
    change state.pc + 4 = _
    rw [pc]
    change BitVec.ofNat 64 (4484 + 12 * block) + BitVec.ofNat 64 4 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · intro answer
    apply (fetched (cursorReplyState state false answer) block blockBound).2.2
    change state.pc + 4 + 4 = _
    rw [pc, BitVec.add_assoc]
    change BitVec.ofNat 64 (4484 + 12 * block) + BitVec.ofNat 64 8 = _
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  · intro answer
    have input : (cursorReplyState state false answer).getReg .x10 =
        state.getReg .x10 := by
      rw [cursorReplyState, writeBits_register]
      rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      input]
    change some (((cursorReplyState state false answer).setReg .x10
      (state.getReg .x10 + signExtend12 32)).setPC (state.pc + 4 + 4 + 4)) =
      some (cursorNextState state false answer)
    simp [signExtend12, cursorNextState, BitVec.add_assoc]

/-- Prefix execution uses the physical pointer after every arbitrary reply. -/
theorem contiguous_prefix_execute (image : Image) (fetched : ContiguousPrefixFetched image)
    (state : MachineState) (first cursor count : Nat)
    (blocks : first + count ≤ 7)
    (pc : state.pc = BitVec.ofNat 64 (4484 + 12 * first))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 32 * count + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 * count + fuel) state allowCoins =
      (do let finished ← cursorPrefix state cursor count
          let result ← execute image fuel finished allowCoins
          return result.charge (10 * count) count) := by
  induction count generalizing state first cursor with
  | zero => simp [cursorPrefix, Execution.charge]
  | succ count ih =>
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      contiguous_prefix_block image fetched state first cursor (by omega) pc pointer
        ready aligned (by omega) heapValid]
    simp only [cursorPrefix, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    have nextPC : (cursorNextState state false answer).pc =
        BitVec.ofNat 64 (4484 + 12 * (first + 1)) := by
      rw [cursor_next_pc, pc]
      change BitVec.ofNat 64 (4484 + 12 * first) + BitVec.ofNat 64 12 = _
      rw [← BitVec.ofNat_add]
      congr 1 <;> omega
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

end CommitGolfCandidate
