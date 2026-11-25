import CommitGolfCandidate.UnrolledSegment

/-! A block is four segments (256 leaves), a heap-end branch and two long jumps.
Every block costs 7946 instructions and 22282 cycles, including its final jump. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem unrolled_segment_start (start : Word) (segment : Nat) :
    start + BitVec.ofNat 64 (7944 * segment) + 7944 =
      start + BitVec.ofNat 64 (7944 * (segment + 1)) := by
  rw [show 7944 * (segment + 1) = 7944 * segment + 7944 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  rfl

theorem unrolled_segments (image : Image) (start : Word)
    (fetched : ∀ segment < 4, UnrolledSegmentFetched image (start + BitVec.ofNat 64 (7944 * segment)))
    (state : MachineState) (first count remaining : Nat) (messageBase : Word)
    (fits : first + count ≤ 4) (progress : UnrolledProgress state (remaining + 64 * count))
    (fuel : Nat) :
    execute image (1986 * count + fuel)
      (cursorNormalize state messageBase (start + BitVec.ofNat 64 (7944 * first))) true =
      (do let finished ← commitLeaves state (64 * count)
          let result ← execute image fuel
            (cursorNormalize finished messageBase (start + BitVec.ofNat 64 (7944 * (first + count)))) true
          return result.charge (5570 * count) (512 * count)) := by
  induction count generalizing state first with
  | zero => simp [commitLeaves, Execution.charge]
  | succ count ih =>
    rw [show 1986 * (count + 1) + fuel = 1986 + (1986 * count + fuel) by omega,
      unrolled_segment image _ (fetched first (by omega)) state (remaining + 64 * count) messageBase
        (by rw [show remaining + 64 * count + 64 = remaining + 64 * (count + 1) by ring]; exact progress),
      show 64 * (count + 1) = 64 + 64 * count by omega, unrolled_leaves_split]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    rw [unrolled_segment_start,
      ih middle (first + 1) (by omega)
        (unrolled_progress_leaves state 64 (remaining + 64 * count)
          (by rw [show remaining + 64 * count + 64 = remaining + 64 * (count + 1) by ring]; exact progress)
          middle reached)]
    simp only [bind_assoc, pure_bind, show first + 1 + count = first + (count + 1) by omega]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (cursorNormalize finished messageBase
        (start + BitVec.ofNat 64 (7944 * (first + (count + 1))))) true >>= continuation)
    funext result
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

def UnrolledBlockFetched (image : Image) (start : Word) (exitOffset loopOffset : BitVec 21) : Prop :=
  (∀ segment < 4, UnrolledSegmentFetched image (start + BitVec.ofNat 64 (7944 * segment))) ∧
  (∀ state : MachineState, state.pc = start + 31776 →
    fetch image state = some (.base (.BLTU .x23 .x22 8))) ∧
  (∀ state : MachineState, state.pc = start + 31780 →
    fetch image state = some (.base (.JAL .x0 exitOffset))) ∧
  (∀ state : MachineState, state.pc = start + 31784 →
    fetch image state = some (.base (.JAL .x0 loopOffset)))

theorem unrolled_heap_branch (heap ending : Word) (remaining : Nat)
    (window : heap.toNat + 32 * remaining = ending.toNat) :
    BitVec.ult heap ending = decide (0 < remaining) := by
  simp only [BitVec.ult]
  by_cases empty : remaining = 0
  · subst empty
    simp only [Nat.mul_zero, Nat.add_zero] at window
    simp [window]
  · have positive : heap.toNat < ending.toNat := by omega
    simp [positive, Nat.pos_of_ne_zero empty]

theorem unrolled_normalize_pc (state : MachineState) (messageBase pc : Word) :
    (cursorNormalize state messageBase pc).pc = pc := rfl

theorem unrolled_normalize_set_pc (state : MachineState) (messageBase pc next : Word) :
    (cursorNormalize state messageBase pc).setPC next = cursorNormalize state messageBase next := rfl

theorem unrolled_normalize_register (state : MachineState) (messageBase pc : Word) (reg : Reg)
    (preserved : reg ∉ [Reg.x8, .x21, .x10, .x20]) :
    (cursorNormalize state messageBase pc).getReg reg = state.getReg reg := by
  unfold cursorNormalize
  rw [MachineState.getReg_setPC]
  exact cursor_frame_register state messageBase reg preserved

theorem unrolled_branch_step (state : MachineState) (offset : BitVec 13) :
    ordinaryStep state (.base (.BLTU .x23 .x22 offset)) =
      some (if BitVec.ult (state.getReg .x23) (state.getReg .x22)
        then state.setPC (state.pc + signExtend13 offset) else state.setPC (state.pc + 4)) := rfl

theorem unrolled_jump_step (state : MachineState) (offset : BitVec 21) :
    ordinaryStep state (.base (.JAL .x0 offset)) =
      some (state.setPC (state.pc + signExtend21 offset)) := rfl

/-- The heap-end branch selects the exit or loop jump: two instructions, two cycles. -/
theorem unrolled_branch (image : Image) (start : Word) (exitOffset loopOffset : BitVec 21)
    (fetched : UnrolledBlockFetched image start exitOffset loopOffset)
    (exitJump : start + 31780 + signExtend21 exitOffset = 4364)
    (loopJump : start + 31784 + signExtend21 loopOffset = start)
    (state : MachineState) (remaining : Nat) (messageBase : Word)
    (window : (state.getReg .x23).toNat + 32 * remaining = (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute image (2 + fuel) (cursorNormalize state messageBase (start + 31776)) true =
      (do let result ← execute image fuel
            (cursorNormalize state messageBase (if remaining = 0 then 4364 else start)) true
          return result.charge 2 0) := by
  have branch := unrolled_branch_step (cursorNormalize state messageBase (start + 31776)) 8
  rw [unrolled_normalize_register state messageBase _ .x23 (by decide),
    unrolled_normalize_register state messageBase _ .x22 (by decide),
    unrolled_heap_branch _ _ remaining window, unrolled_normalize_pc,
    unrolled_normalize_set_pc, unrolled_normalize_set_pc] at branch
  have branchFetched : fetch image (cursorNormalize state messageBase (start + 31776)) =
      some (.base (.BLTU .x23 .x22 8)) :=
    fetched.2.1 _ (unrolled_normalize_pc state messageBase _)
  by_cases empty : remaining = 0
  · have stepped : ordinaryStep (cursorNormalize state messageBase (start + 31776))
        (.base (.BLTU .x23 .x22 8)) = some (cursorNormalize state messageBase (start + 31780)) := by
      rw [branch]
      simp only [empty, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
      rw [BitVec.add_assoc]
      rfl
    have jumpFetched : fetch image (cursorNormalize state messageBase (start + 31780)) =
        some (.base (.JAL .x0 exitOffset)) :=
      fetched.2.2.1 _ (unrolled_normalize_pc state messageBase _)
    have jumped : ordinaryStep (cursorNormalize state messageBase (start + 31780))
        (.base (.JAL .x0 exitOffset)) = some (cursorNormalize state messageBase 4364) := by
      rw [unrolled_jump_step, unrolled_normalize_pc, exitJump, unrolled_normalize_set_pc]
    rw [show 2 + fuel = (fuel + 1) + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ branchFetched stepped,
      execute_ordinary_step _ _ _ _ _ _ jumpFetched jumped]
    simp [empty, Execution.charge, instructionCycles, ← Nat.add_assoc]
  · have stepped : ordinaryStep (cursorNormalize state messageBase (start + 31776))
        (.base (.BLTU .x23 .x22 8)) = some (cursorNormalize state messageBase (start + 31784)) := by
      rw [branch]
      simp only [Nat.pos_of_ne_zero empty, decide_true, ite_true]
      rw [show signExtend13 (8 : BitVec 13) = (8 : Word) by decide, BitVec.add_assoc]
      rfl
    have jumpFetched : fetch image (cursorNormalize state messageBase (start + 31784)) =
        some (.base (.JAL .x0 loopOffset)) :=
      fetched.2.2.2 _ (unrolled_normalize_pc state messageBase _)
    have jumped : ordinaryStep (cursorNormalize state messageBase (start + 31784))
        (.base (.JAL .x0 loopOffset)) = some (cursorNormalize state messageBase start) := by
      rw [unrolled_jump_step, unrolled_normalize_pc, loopJump, unrolled_normalize_set_pc]
    rw [show 2 + fuel = (fuel + 1) + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ branchFetched stepped,
      execute_ordinary_step _ _ _ _ _ _ jumpFetched jumped]
    simp [empty, Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem unrolled_charge_charge (result : Execution) (first firstCalls second secondCalls : Nat) :
    (result.charge first firstCalls).charge second secondCalls =
      result.charge (second + first) (secondCalls + firstCalls) := by
  simp [Execution.charge, Nat.add_assoc]

/-- One block of 256 leaves: 7946 instructions, 22282 cycles and 2048 queries. -/
theorem unrolled_block (image : Image) (start : Word) (exitOffset loopOffset : BitVec 21)
    (fetched : UnrolledBlockFetched image start exitOffset loopOffset)
    (exitJump : start + 31780 + signExtend21 exitOffset = 4364)
    (loopJump : start + 31784 + signExtend21 loopOffset = start)
    (state : MachineState) (remaining : Nat) (messageBase : Word)
    (progress : UnrolledProgress state (remaining + 256)) (fuel : Nat) :
    execute image (7946 + fuel) (cursorNormalize state messageBase start) true =
      (do let finished ← commitLeaves state 256
          let result ← execute image fuel
            (cursorNormalize finished messageBase (if remaining = 0 then 4364 else start)) true
          return result.charge 22282 2048) := by
  have segmentsRun := unrolled_segments image start fetched.1 state 0 4 remaining messageBase
    (by decide) progress (2 + fuel)
  rw [show start + BitVec.ofNat 64 (7944 * 0) = start by simp] at segmentsRun
  rw [show 7946 + fuel = 1986 * 4 + (2 + fuel) by omega, segmentsRun]
  apply bind_congr_of_forall_mem_support
  intro finished reached
  have finishedProgress := unrolled_progress_leaves state (64 * 4) remaining progress finished reached
  rw [show start + BitVec.ofNat 64 (7944 * (0 + 4)) = start + 31776 from rfl,
    unrolled_branch image start exitOffset loopOffset fetched exitJump loopJump finished remaining
      messageBase finishedProgress.window]
  simp [Execution.charge, ← Nat.add_assoc]

/-- All blocks of the leaf phase, ending at the parent setup. -/
theorem unrolled_loop (image : Image) (start : Word) (exitOffset loopOffset : BitVec 21)
    (fetched : UnrolledBlockFetched image start exitOffset loopOffset)
    (exitJump : start + 31780 + signExtend21 exitOffset = 4364)
    (loopJump : start + 31784 + signExtend21 loopOffset = start)
    (state : MachineState) (blocks : Nat) (messageBase : Word)
    (progress : UnrolledProgress state (256 * (blocks + 1))) (fuel : Nat) :
    execute image (7946 * (blocks + 1) + fuel) (cursorNormalize state messageBase start) true =
      (do let finished ← commitLeaves state (256 * (blocks + 1))
          let result ← execute image fuel (cursorNormalize finished messageBase 4364) true
          return result.charge (22282 * (blocks + 1)) (2048 * (blocks + 1))) := by
  induction blocks generalizing state with
  | zero =>
    have run := unrolled_block image start exitOffset loopOffset fetched exitJump loopJump
      state 0 messageBase (by simpa using progress) fuel
    simpa using run
  | succ blocks ih =>
    rw [show 7946 * (blocks + 1 + 1) + fuel = 7946 + (7946 * (blocks + 1) + fuel) by ring,
      unrolled_block image start exitOffset loopOffset fetched exitJump loopJump
        state (256 * (blocks + 1)) messageBase
        (by simpa only [show 256 * (blocks + 1) + 256 = 256 * (blocks + 1 + 1) by ring] using progress),
      show 256 * (blocks + 1 + 1) = 256 + 256 * (blocks + 1) by ring, unrolled_leaves_split]
    simp only [show 256 * (blocks + 1) ≠ 0 by omega, ite_false, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    rw [ih middle (unrolled_progress_leaves state 256 (256 * (blocks + 1))
      (by simpa only [show 256 * (blocks + 1) + 256 = 256 * (blocks + 1 + 1) by ring] using progress)
      middle reached)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (cursorNormalize finished messageBase 4364) true >>= continuation)
    funext result
    rw [unrolled_charge_charge, show 22282 + 22282 * (blocks + 1) = 22282 * (blocks + 1 + 1) by ring,
      show 2048 + 2048 * (blocks + 1) = 2048 * (blocks + 1 + 1) by ring]

end CommitGolfCandidate
