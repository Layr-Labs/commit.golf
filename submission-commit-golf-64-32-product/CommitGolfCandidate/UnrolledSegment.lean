import CommitGolfCandidate.UnrolledPosition

/-! A segment is 64 unrolled leaves followed by one salt-base advance and a heap
rebase from the last reply address. It returns to the reference frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem unrolled_leaves_split (state : MachineState) (first second : Nat) :
    commitLeaves state (first + second) =
      (do let middle ← commitLeaves state first
          commitLeaves middle second) := by
  induction first generalizing state with
  | zero => simp [commitLeaves]
  | succ first ih =>
    rw [show first + 1 + second = (first + second) + 1 by omega]
    simp only [commitLeaves, bind_assoc]
    apply congrArg (fun continuation => commitPositionRun state >>= continuation)
    funext next
    exact ih next

/-- Every reference leaf leaves its heap reply address in x12, one slot below x23. -/
theorem unrolled_position_output (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x12 + 32 = finished.getReg .x23 := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reachable
  obtain ⟨leaf, member, rfl⟩ := reachable
  simp only [commitLeafLoop, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at member
  obtain ⟨body, reached, rfl⟩ := member
  simp only [heapStreamingMachineBlocks, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at reached
  obtain ⟨prefixState, _, answer, _, rfl⟩ := reached
  rfl

structure UnrolledProgress (state : MachineState) (remaining : Nat) : Prop where
  invariant : CommitLeavesInvariant state remaining
  link : state.getReg .x1 = 4316
  window : (state.getReg .x23).toNat + 32 * remaining = (state.getReg .x22).toNat

theorem unrolled_progress_next (state finished : MachineState) (remaining : Nat)
    (progress : UnrolledProgress state (remaining + 1))
    (reachable : finished ∈ support (commitPositionRun state)) :
    UnrolledProgress finished remaining :=
  ⟨commit_leaves_next_invariant state finished remaining progress.invariant reachable,
    contiguous_position_link state finished reachable,
    outer_heap_progress_next state finished remaining progress.window reachable⟩

theorem unrolled_progress_leaves (state : MachineState) (count remaining : Nat)
    (progress : UnrolledProgress state (remaining + count)) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state count)) :
    UnrolledProgress finished remaining := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact progress
  | succ count ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    exact ih next (unrolled_progress_next state next (remaining + count)
      (by simpa only [Nat.add_assoc] using progress) reached) rest

theorem unrolled_leaves_output (state : MachineState) (count : Nat) (positive : 0 < count)
    (finished : MachineState) (reachable : finished ∈ support (commitLeaves state count)) :
    finished.getReg .x12 + 32 = finished.getReg .x23 := by
  induction count generalizing state with
  | zero => omega
  | succ count ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    cases count with
    | zero =>
      simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at rest
      subst finished
      exact unrolled_position_output state next reached
    | succ count => exact ih next (by omega) rest

def UnrolledLeavesFetched (image : Image) (start : Word) : Prop :=
  ∀ slot < 64, UnrolledSaltFetched image slot (start + BitVec.ofNat 64 (124 * slot)) ∧
    UnrolledBlocksFetched image slot (start + BitVec.ofNat 64 (124 * slot) + 28)

theorem unrolled_leaf_start (start : Word) (slot : Nat) :
    start + BitVec.ofNat 64 (124 * slot) + 124 = start + BitVec.ofNat 64 (124 * (slot + 1)) := by
  rw [show 124 * (slot + 1) = 124 * slot + 124 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  rfl

/-- Consecutive unrolled leaves: 31 instructions, 87 cycles and eight queries each. -/
theorem unrolled_leaves (image : Image) (start : Word) (fetched : UnrolledLeavesFetched image start)
    (state : MachineState) (slot count remaining : Nat) (messageBase : Word)
    (fits : slot + count ≤ 64) (progress : UnrolledProgress state (remaining + count))
    (fuel : Nat) :
    execute image (31 * count + fuel)
      (unrolledShift slot (cursorNormalize state messageBase (start + BitVec.ofNat 64 (124 * slot))))
        true =
      (do let finished ← commitLeaves state count
          let result ← execute image fuel
            (unrolledShift (slot + count)
              (cursorNormalize finished messageBase (start + BitVec.ofNat 64 (124 * (slot + count)))))
            true
          return result.charge (87 * count) (8 * count)) := by
  induction count generalizing state slot with
  | zero => simp [commitLeaves, Execution.charge]
  | succ count ih =>
    have invariant := progress.invariant
    rw [show 31 * (count + 1) + fuel = 31 + (31 * count + fuel) by omega,
      unrolled_position image slot (by omega) (start + BitVec.ofNat 64 (124 * slot))
        (fetched slot (by omega)).1 (fetched slot (by omega)).2 state messageBase
        progress.link invariant.scratch invariant.sourceAbove invariant.oracleReady
        (fun word => invariant.salts word.val (by omega))
        (fun word => invariant.heap word.val (by omega))
        (fun word bound => invariant.message word (by omega)),
      unrolled_leaf_start]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (slot + 1) (by omega)
      (unrolled_progress_next state next (remaining + count)
        (by simpa only [Nat.add_assoc] using progress) reached)]
    simp only [bind_assoc, pure_bind, show slot + 1 + count = slot + (count + 1) by omega]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply congrArg (fun continuation =>
      execute image fuel (unrolledShift (slot + (count + 1))
        (cursorNormalize finished messageBase
          (start + BitVec.ofNat 64 (124 * (slot + (count + 1)))))) true >>= continuation)
    funext result
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

def UnrolledSegmentFetched (image : Image) (start : Word) : Prop :=
  UnrolledLeavesFetched image start ∧
  (∀ state : MachineState, state.pc = start + 7936 →
    fetch image state = some (.base (.ADDI .x18 .x18 1536))) ∧
  (∀ state : MachineState, state.pc = start + 7940 →
    fetch image state = some (.base (.ADDI .x23 .x12 32)))

/-- Advance the salt base by 64 nonces and rebase the heap pointer past the
last reply slot: the live frame is again the reference frame. -/
theorem unrolled_rebase_frame (state : MachineState) (messageBase pc : Word)
    (output : state.getReg .x12 + 32 = state.getReg .x23) :
    execInstrBr (execInstrBr (unrolledShift 64 (cursorNormalize state messageBase pc))
        (.ADDI .x18 .x18 1536)) (.ADDI .x23 .x12 32) =
      cursorNormalize state messageBase (pc + 8) := by
  have salt : (unrolledShift 64 (cursorNormalize state messageBase pc)).getReg .x18 +
      signExtend12 1536 = state.getReg .x18 := by
    rw [unrolled_shift_salt]
    change state.getReg .x18 - BitVec.ofNat 64 (24 * 64) + signExtend12 1536 = _
    rw [show signExtend12 (1536 : BitVec 12) = BitVec.ofNat 64 (24 * 64) by decide,
      BitVec.sub_add_cancel]
  simp only [execInstrBr]
  rw [salt]
  have reply : ((((unrolledShift 64 (cursorNormalize state messageBase pc)).setReg .x18
      (state.getReg .x18)).setPC ((unrolledShift 64 (cursorNormalize state messageBase pc)).pc + 4)).getReg .x12) +
        signExtend12 32 = state.getReg .x23 := by
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      unrolled_shift_register _ _ .x12 (by decide) (by decide),
      show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]
    exact output
  rw [reply]
  cases state
  dsimp [unrolledShift, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  congr 1
  · funext reg
    cases reg <;> rfl
  · rw [BitVec.add_assoc]
    rfl

theorem unrolled_rebase_execute (image : Image) (start : Word)
    (fetched : UnrolledSegmentFetched image start) (state : MachineState) (messageBase : Word)
    (output : state.getReg .x12 + 32 = state.getReg .x23) (fuel : Nat) :
    execute image (2 + fuel)
      (unrolledShift 64 (cursorNormalize state messageBase (start + 7936))) true =
      (do let result ← execute image fuel (cursorNormalize state messageBase (start + 7944)) true
          return result.charge 2 0) := by
  let first := unrolledShift 64 (cursorNormalize state messageBase (start + 7936))
  let second := execInstrBr first (.ADDI .x18 .x18 1536)
  have firstFetched : fetch image first = some (.base (.ADDI .x18 .x18 1536)) :=
    fetched.2.1 first rfl
  have secondFetched : fetch image second = some (.base (.ADDI .x23 .x12 32)) := by
    apply fetched.2.2 second
    change start + 7936 + 4 = start + 7940
    rw [BitVec.add_assoc]
    rfl
  have firstStep : ordinaryStep first (.base (.ADDI .x18 .x18 1536)) = some second := rfl
  have secondStep : ordinaryStep second (.base (.ADDI .x23 .x12 32)) =
      some (cursorNormalize state messageBase (start + 7944)) := by
    change some (execInstrBr second (.ADDI .x23 .x12 32)) = _
    rw [unrolled_rebase_frame state messageBase (start + 7936) output, BitVec.add_assoc]
    rfl
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ firstFetched firstStep,
    execute_ordinary_step _ _ _ _ _ _ secondFetched secondStep]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

/-- One segment: 1986 instructions, 5570 cycles and 512 queries. -/
theorem unrolled_segment (image : Image) (start : Word) (fetched : UnrolledSegmentFetched image start)
    (state : MachineState) (remaining : Nat) (messageBase : Word)
    (progress : UnrolledProgress state (remaining + 64)) (fuel : Nat) :
    execute image (1986 + fuel) (cursorNormalize state messageBase start) true =
      (do let finished ← commitLeaves state 64
          let result ← execute image fuel (cursorNormalize finished messageBase (start + 7944)) true
          return result.charge 5570 512) := by
  have leavesRun := unrolled_leaves image start fetched.1 state 0 64 remaining messageBase
    (by decide) progress (2 + fuel)
  rw [unrolled_shift_zero, show start + BitVec.ofNat 64 (124 * 0) = start by simp] at leavesRun
  rw [show 1986 + fuel = 31 * 64 + (2 + fuel) by omega, leavesRun]
  apply bind_congr_of_forall_mem_support
  intro finished reached
  rw [show 0 + 64 = 64 from rfl, show BitVec.ofNat 64 (124 * 64) = (7936 : Word) from rfl,
    unrolled_rebase_execute image start fetched finished messageBase
      (unrolled_leaves_output state 64 (by decide) finished reached)]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
