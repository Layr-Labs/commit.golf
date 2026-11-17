import CommitGolfCandidate.ContiguousLoop
import CommitGolfCandidate.UnrolledReloc

/-! The unrolled leaf loop. Thirty-two relocated leaf bodies run back to back; one
three-instruction latch per group advances the nonce and heap registers and repeats
the group until the heap end. Each leaf reuses the proved original body through the
relocation simulation; the reference still supplies virtual per-leaf progress. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The original 31 instructions of one leaf, stopped before any latch. -/
theorem unrolled_base_leaf (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (state : MachineState) (messageBase : Word)
    (link : state.getReg .x1 = 4316)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (above : 32 ≤ (state.getReg .x8).toNat)
    (oracleReady : CommitLeafOracleReady state)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (31 + fuel) (cursorNormalize state messageBase 4456) true =
      (do let leaf ← commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize leaf messageBase 4580) true
          return result.charge 87 8) := by
  let cursor := (state.getReg .x8).toNat - 32
  let ready := commitPositionState state
  obtain ⟨aligned, bounded⟩ := commit_leaf_source_range state messageValid
  have chain : state.getReg .x21 = BitVec.ofNat 64 cursor := by
    rw [scratch]
    calc
      state.getReg .x8 - 32 = BitVec.ofNat 64 (state.getReg .x8).toNat -
          BitVec.ofNat 64 32 := by simp
      _ = _ := BitVec.ofNat_sub_ofNat_of_le (w := 64) _ 32 (by decide) above
  have source : state.getReg .x8 = BitVec.ofNat 64 (cursor + 32) := by
    have natural : cursor + 32 = (state.getReg .x8).toNat := by dsimp [cursor]; omega
    rw [natural]; simp
  have destinationValid : ∀ word : Fin 4,
      accessValid ((cursorNormalize state messageBase 4456).getReg .x10 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    change accessValid ((cursorLeafFrame state messageBase).getReg .x10 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true
    rw [cursor_frame_pointer, chain, ← BitVec.ofNat_add]
    have small : cursor + 8 * word.val < 2 ^ 64 := by
      have hw := word.isLt
      dsimp [cursor]
      unfold MEMORY_BYTES at bounded
      omega
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have hw := word.isLt; dsimp [cursor]; omega
    · dsimp [cursor]; omega
  have physicalSalt : ∀ word : Fin 4,
      accessValid ((cursorNormalize state messageBase 4456).getReg .x18 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    change ∀ word : Fin 4, accessValid ((cursorLeafFrame state messageBase).getReg .x18 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true
    rw [cursor_frame_register state messageBase .x18 (by decide)]
    exact saltValid
  have readySource : ready.getReg .x8 = state.getReg .x8 :=
    commit_position_register state .x8 (by decide) (by decide)
  have readyChain : ready.getReg .x21 = BitVec.ofNat 64 cursor :=
    (commit_position_register state .x21 (by decide) (by decide)).trans chain
  have readyOracle : StreamingOracleReady (cursorLeafFrame ready messageBase) := by
    rcases oracleReady with ⟨r5, r11, r13⟩
    exact ⟨(cursor_frame_register ready messageBase .x5 (by decide)).trans
        ((commit_position_register state .x5 (by decide) (by decide)).trans r5),
      (cursor_frame_register ready messageBase .x11 (by decide)).trans
        ((commit_position_register state .x11 (by decide) (by decide)).trans r11),
      (cursor_frame_register ready messageBase .x13 (by decide)).trans
        ((commit_position_register state .x13 (by decide) (by decide)).trans r13)⟩
  have readyHeap : rangeValid ((cursorLeafFrame ready messageBase).getReg .x23) 32 = true ∧
      ((cursorLeafFrame ready messageBase).getReg .x23).toNat % 8 = 0 := by
    rw [cursor_frame_register ready messageBase .x23 (by decide),
      commit_position_register state .x23 (by decide) (by decide)]
    exact commit_leaf_heap_range state heapValid
  have leafRun := contiguous_leaf_blocks (submission.image .commit) prefixFetched tailFetched
    ((cursorLeafFrame ready messageBase).setPC 4484) cursor rfl
    (by rw [MachineState.getReg_setPC, cursor_frame_pointer]; exact readyChain)
    (by simpa only [StreamingOracleReady, MachineState.getReg_setPC] using readyOracle)
    (by dsimp [cursor]; omega) (by dsimp [cursor]; omega)
    (by simpa only [MachineState.getReg_setPC] using readyHeap) fuel true
  rw [show 31 + fuel = 7 + (24 + fuel) by omega,
    contiguous_salt_execute _ saltFetched _ rfl physicalSalt destinationValid,
    contiguous_salt_ready state messageBase link, leafRun]
  rw [contiguous_heap_pc_bind (cursorLeafFrame ready messageBase) cursor 4484 4580
    (fun finished => do
      let result ← execute (submission.image .commit) fuel finished true
      return result.charge 80 8)]
  rw [fused_leaf_reference_bind ready
    cursor (readySource.trans source) readyChain
    (by
      change (ready.getReg .x8).toNat - 32 = cursor
      rw [readySource]) messageBase 4580
    (fun finished => do
      let result ← execute (submission.image .commit) fuel finished true
      return result.charge 80 8)]
  simp only [commitLeafReadyState, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf _
  simp [Execution.charge, ← Nat.add_assoc]

/-- First instruction of leaf `u` in the group. -/
def unrolledLeafPC (u : Nat) : Word := BitVec.ofNat 64 (1011404 + 124 * u)

/-- Physical state at leaf `u` of a group, for the virtual per-leaf state `state`. -/
def unrolledState (u : Nat) (state : MachineState) (messageBase : Word) : MachineState :=
  unrolledShift u (cursorLeafFrame state messageBase) (unrolledLeafPC u)

theorem unrolled_add_sub (x a k : Word) : x + k - (a + k) = x - a := by
  first
    | bv_omega
    | exact add_sub_add_right_eq_sub x a k

theorem unrolled_nonce_lag (u : Nat) (x : Word) :
    x - BitVec.ofNat 64 (24 * u) = x + 24 - BitVec.ofNat 64 (24 * (u + 1)) := by
  rw [show 24 * (u + 1) = 24 * u + 24 by omega, BitVec.ofNat_add]
  exact (unrolled_add_sub x _ 24).symm

theorem unrolled_heap_lag (u : Nat) (x : Word) :
    x - BitVec.ofNat 64 (32 * u) = x + 32 - BitVec.ofNat 64 (32 * (u + 1)) := by
  rw [show 32 * (u + 1) = 32 * u + 32 by omega, BitVec.ofNat_add]
  exact (unrolled_add_sub x _ 32).symm

/-- After leaf `u`, the lagging physical state is already leaf `u+1` of the advanced
reference state: the per-leaf pointer advance is absorbed by the next immediates. -/
theorem unrolled_frame (u : Nat) (leaf : MachineState) (messageBase : Word) :
    unrolledMove u (unrolledDelta u) (cursorNormalize leaf messageBase 4580) =
      unrolledState (u + 1) (commitPositionNextState (leaf.setPC 4348)) messageBase := by
  refine unrolled_state_congr leaf _ _ _ _ _ _ ?_ rfl ?_
  · funext reg
    cases reg <;> first
      | rfl
      | exact unrolled_nonce_lag u _
      | exact unrolled_heap_lag u _
  · show BitVec.ofNat 64 4580 + BitVec.ofNat 64 (1006948 + 124 * u) =
      BitVec.ofNat 64 (1011404 + 124 * (u + 1))
    rw [← BitVec.ofNat_add]
    congr 1
    omega

theorem unrolled_start (u : Nat) (state : MachineState) (messageBase : Word) :
    unrolledMove u (unrolledDelta u) (cursorNormalize state messageBase 4456) =
      unrolledState u state messageBase := by
  show unrolledShift u (cursorLeafFrame state messageBase)
      (BitVec.ofNat 64 4456 + BitVec.ofNat 64 (1006948 + 124 * u)) =
    unrolledShift u (cursorLeafFrame state messageBase) (BitVec.ofNat 64 (1011404 + 124 * u))
  rw [← BitVec.ofNat_add]
  congr 2
  omega

/-- One relocated leaf: 31 instructions, 87 cycles and eight queries, with the reference
leaf transition and no latch. -/
theorem unrolled_position (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (u : Nat) (hu : u < 64) (state : MachineState) (messageBase : Word)
    (link : state.getReg .x1 = 4316)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (above : 32 ≤ (state.getReg .x8).toNat)
    (oracleReady : CommitLeafOracleReady state)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (31 + fuel) (unrolledState u state messageBase) true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel
            (unrolledState (u + 1) finished messageBase) true
          return result.charge 87 8) := by
  have base : execute (submission.image .commit) 31
      (cursorNormalize state messageBase 4456) true = _ :=
    unrolled_base_leaf saltFetched prefixFetched tailFetched state messageBase link scratch
      above oracleReady saltValid heapValid messageValid 0
  have moved := unrolled_reloc u hu true 31 0 rfl (cursorNormalize state messageBase 4456) rfl
  rw [execute_add, ← unrolled_start u state messageBase, moved, base]
  simp only [execute, commitPositionRun, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp]
  apply bind_congr_of_forall_mem_support
  intro leaf _
  rw [← unrolled_frame u leaf messageBase]
  simp [resume, unrolledLift, Execution.charge]

/-- Consecutive leaves of one group. -/
theorem unrolled_leaves (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (count u : Nat) (inside : u + count ≤ 64) (state : MachineState) (remaining : Nat)
    (messageBase : Word)
    (invariant : CommitLeavesInvariant state (count + remaining))
    (link : state.getReg .x1 = 4316) (fuel : Nat) :
    execute (submission.image .commit) (31 * count + fuel)
        (unrolledState u state messageBase) true =
      (do let finished ← commitLeaves state count
          let result ← execute (submission.image .commit) fuel
            (unrolledState (u + count) finished messageBase) true
          return result.charge (87 * count) (8 * count)) := by
  induction count generalizing u state fuel with
  | zero => simp [commitLeaves, Execution.charge]
  | succ count ih =>
    have current : CommitLeavesInvariant state (count + remaining + 1) := by
      rw [show count + remaining + 1 = count + 1 + remaining by omega]
      exact invariant
    rw [show 31 * (count + 1) + fuel = 31 + (31 * count + fuel) by omega,
      unrolled_position saltFetched prefixFetched tailFetched u (by omega) state messageBase link
        current.scratch current.sourceAbove current.oracleReady
        (fun word => current.salts word.val (by omega))
        (fun word => current.heap word.val (by omega))
        (fun word bound => current.message word (by omega))]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [show u + (count + 1) = u + 1 + count by omega,
      ih (u + 1) (by omega) next
        (commit_leaves_next_invariant state next (count + remaining) current reached)
        (contiguous_position_link state next reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Reference progress across several leaves: invariant, link and heap window. -/
theorem unrolled_leaves_progress (count : Nat) (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (count + remaining))
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * (count + remaining) =
      (state.getReg .x22).toNat)
    (finished : MachineState) (reached : finished ∈ support (commitLeaves state count)) :
    CommitLeavesInvariant finished remaining ∧ finished.getReg .x1 = 4316 ∧
      (finished.getReg .x23).toNat + 32 * remaining = (finished.getReg .x22).toNat := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    exact ⟨by simpa using invariant, link, by simpa using window⟩
  | succ count ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reached
    obtain ⟨next, nextReached, finishedReached⟩ := reached
    have current : CommitLeavesInvariant state (count + remaining + 1) := by
      rw [show count + remaining + 1 = count + 1 + remaining by omega]
      exact invariant
    have currentWindow : (state.getReg .x23).toNat + 32 * (count + remaining + 1) =
        (state.getReg .x22).toNat := by omega
    exact ih next
      (commit_leaves_next_invariant state next (count + remaining) current nextReached)
      (contiguous_position_link state next nextReached)
      (outer_heap_progress_next state next (count + remaining) currentWindow nextReached)
      finishedReached

theorem unrolled_leaves_add (first second : Nat) (state : MachineState) :
    commitLeaves state (first + second) =
      (do let middle ← commitLeaves state first
          commitLeaves middle second) := by
  induction first generalizing state with
  | zero => simp [commitLeaves]
  | succ first ih =>
    rw [show first + 1 + second = first + second + 1 by omega]
    simp only [commitLeaves, bind_assoc, ih]

/-! ### Group latch -/

/-- The state after the three pointer advances of the group latch. -/
def unrolledLatchState (state : MachineState) (messageBase : Word) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (unrolledState 64 state messageBase) (.ADDI .x18 .x18 1536))
    (.ADDI .x23 .x23 1024)) (.ADDI .x23 .x23 1024)

theorem unrolled_latch_first (x a b : Word) (same : b = a) : x - a + b = x - 0 := by
  subst same
  rw [BitVec.sub_add_cancel]
  first
    | exact (BitVec.sub_zero x).symm
    | simp

theorem unrolled_latch_last (x a b : Word) (same : b = a) : x - a + b = x := by
  subst same
  rw [BitVec.sub_add_cancel]

theorem unrolled_latch_heap (x : Word) :
    x - BitVec.ofNat 64 (32 * 64) + signExtend12 1024 + signExtend12 1024 = x := by
  rw [BitVec.add_assoc]
  exact unrolled_latch_last x _ _ (by decide)

theorem unrolled_latch_heap0 (x : Word) :
    x - BitVec.ofNat 64 (32 * 64) + signExtend12 1024 + signExtend12 1024 = x - 0 := by
  rw [unrolled_latch_heap]
  first
    | exact (BitVec.sub_zero x).symm
    | simp

theorem unrolled_latch_registers (state : MachineState) (messageBase : Word) :
    (unrolledLatchState state messageBase).getReg .x23 = state.getReg .x23 ∧
    (unrolledLatchState state messageBase).getReg .x22 = state.getReg .x22 := by
  constructor
  · exact unrolled_latch_heap (state.getReg .x23)
  · rfl

/-- Branch after the latch: back toward the re-entry jump while heap remains, else
fall through to the exit jump. -/
theorem unrolled_latch_branch (state : MachineState) (messageBase : Word) :
    execInstrBr (unrolledLatchState state messageBase) (.BLTU .x23 .x22 8) =
      if BitVec.ult (state.getReg .x23) (state.getReg .x22) = true
        then unrolledShift 0 (cursorLeafFrame state messageBase) 1019360
        else cursorNormalize state messageBase 1019356 := by
  have heap := (unrolled_latch_registers state messageBase).1
  have ending := (unrolled_latch_registers state messageBase).2
  show (if BitVec.ult ((unrolledLatchState state messageBase).getReg .x23)
        ((unrolledLatchState state messageBase).getReg .x22) = true
      then (unrolledLatchState state messageBase).setPC
        ((unrolledLatchState state messageBase).pc + signExtend13 8)
      else (unrolledLatchState state messageBase).setPC
        ((unrolledLatchState state messageBase).pc + 4)) = _
  rw [heap, ending]
  by_cases taken : BitVec.ult (state.getReg .x23) (state.getReg .x22) = true
  · rw [if_pos taken, if_pos taken]
    have target : (unrolledLatchState state messageBase).pc + signExtend13 8 = 1019360 := by
      show (1019352 : Word) + signExtend13 8 = 1019360
      first
        | simp [signExtend13]
        | decide +kernel
    refine unrolled_state_congr state _ _ _ _ _ _ ?_ rfl target
    funext reg
    cases reg <;> first
      | rfl
      | exact unrolled_latch_first _ _ _ rfl
      | exact unrolled_latch_heap0 _
  · rw [if_neg taken, if_neg taken]
    refine unrolled_state_congr state _ _ _ _ _ _ ?_ rfl rfl
    funext reg
    cases reg <;> first
      | rfl
      | exact unrolled_latch_last _ _ _ rfl
      | exact unrolled_latch_heap _

/-- The re-entry jump after a non-final group. -/
theorem unrolled_loop_jump (state : MachineState) (messageBase : Word) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel)
        (unrolledShift 0 (cursorLeafFrame state messageBase) 1019360) true =
      (do let result ← execute (submission.image .commit) fuel (unrolledState 0 state messageBase) true
          return result.charge 1 0) := by
  have stepped : ordinaryStep (unrolledShift 0 (cursorLeafFrame state messageBase) 1019360)
      (.base (.JAL .x0 2089196)) = some (unrolledState 0 state messageBase) := by
    have pc : (unrolledShift 0 (cursorLeafFrame state messageBase) 1019360).pc = 1019360 := rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc,
      reduceIte, Bool.false_eq_true]
    first
      | rfl
      | (simp [unrolledState, unrolledShift, unrolledLeafPC, MachineState.setPC, MachineState.setReg]; rfl)
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_group_loop _ rfl) stepped]
  rfl

/-- Four latch instructions per group of 64 leaves (before the final jump). -/
theorem unrolled_latch (state : MachineState) (messageBase : Word) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) (unrolledState 64 state messageBase) true =
      (do let result ← execute (submission.image .commit) fuel
            (if BitVec.ult (state.getReg .x23) (state.getReg .x22) = true
              then unrolledShift 0 (cursorLeafFrame state messageBase) 1019360
              else cursorNormalize state messageBase 1019356) true
          return result.charge 4 0) := by
  have first : ordinaryStep (unrolledState 64 state messageBase)
      (.base (.ADDI .x18 .x18 1536)) =
      some (execInstrBr (unrolledState 64 state messageBase) (.ADDI .x18 .x18 1536)) := rfl
  have second : ordinaryStep
      (execInstrBr (unrolledState 64 state messageBase) (.ADDI .x18 .x18 1536))
      (.base (.ADDI .x23 .x23 1024)) =
      some (execInstrBr (execInstrBr (unrolledState 64 state messageBase) (.ADDI .x18 .x18 1536))
        (.ADDI .x23 .x23 1024)) := rfl
  have third : ordinaryStep
      (execInstrBr (execInstrBr (unrolledState 64 state messageBase) (.ADDI .x18 .x18 1536))
        (.ADDI .x23 .x23 1024))
      (.base (.ADDI .x23 .x23 1024)) = some (unrolledLatchState state messageBase) := rfl
  have fourth : ordinaryStep (unrolledLatchState state messageBase)
      (.base (.BLTU .x23 .x22 8)) =
      some (execInstrBr (unrolledLatchState state messageBase) (.BLTU .x23 .x22 8)) := rfl
  rw [show 4 + fuel = fuel + 1 + 1 + 1 + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_nonce_step _ rfl) first,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_heap_step _ rfl) second,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_heap_step2 _ rfl) third,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_group_branch _ rfl) fourth,
    unrolled_latch_branch]
  simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

/-- The fall-through jump after the last group enters parent setup. -/
theorem unrolled_exit (state : MachineState) (pc : state.pc = 1019356) (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4364) true
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JAL .x0 1082160)) =
      some (state.setPC 4364) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      pc, MachineState.setReg]
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ (t1_image_group_exit state pc) stepped]
  rfl

/-- One whole group: 64 leaves and the latch branch use 1988 instructions and 5572 cycles. -/
theorem unrolled_group (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (state : MachineState) (messageBase : Word) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (64 + remaining))
    (link : state.getReg .x1 = 4316) (fuel : Nat) :
    execute (submission.image .commit) (1988 + fuel) (unrolledState 0 state messageBase) true =
      (do let middle ← commitLeaves state 64
          let result ← execute (submission.image .commit) fuel
            (if BitVec.ult (middle.getReg .x23) (middle.getReg .x22) = true
              then unrolledShift 0 (cursorLeafFrame middle messageBase) 1019360
              else cursorNormalize middle messageBase 1019356) true
          return result.charge 5572 512) := by
  rw [show 1988 + fuel = 31 * 64 + (4 + fuel) by omega,
    unrolled_leaves saltFetched prefixFetched tailFetched 64 0 (by omega) state remaining
      messageBase invariant link]
  apply bind_congr_of_forall_mem_support
  intro middle _
  rw [show 0 + 64 = 64 from rfl, unrolled_latch middle messageBase]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The whole leaf loop over `groups + 1` groups, including the exit jump. -/
theorem unrolled_groups (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (groups : Nat) (state : MachineState) (messageBase : Word)
    (invariant : CommitLeavesInvariant state (64 * (groups + 1)))
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * (64 * (groups + 1)) =
      (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute (submission.image .commit) (1989 * (groups + 1) + fuel)
        (unrolledState 0 state messageBase) true =
      (do let finished ← commitLeaves state (64 * (groups + 1))
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize finished messageBase 4364) true
          return result.charge (5573 * (groups + 1)) (512 * (groups + 1))) := by
  induction groups generalizing state with
  | zero =>
    have current : CommitLeavesInvariant state (64 + 0) := invariant
    have currentWindow : (state.getReg .x23).toNat + 32 * (64 + 0) =
        (state.getReg .x22).toNat := window
    rw [show 1989 * (0 + 1) + fuel = 1988 + (1 + fuel) by omega,
      unrolled_group saltFetched prefixFetched tailFetched state messageBase 0 current link]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    obtain ⟨_, _, middleWindow⟩ :=
      unrolled_leaves_progress 64 state 0 current link currentWindow middle reached
    have done : ¬ BitVec.ult (middle.getReg .x23) (middle.getReg .x22) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]
      omega
    rw [if_neg done, unrolled_exit _ rfl]
    simp [cursorNormalize, hoist_pc_pc, Execution.charge, ← Nat.add_assoc]
  | succ groups ih =>
    have current : CommitLeavesInvariant state (64 + 64 * (groups + 1)) := by
      rw [show 64 + 64 * (groups + 1) = 64 * (groups + 1 + 1) by omega]
      exact invariant
    have currentWindow : (state.getReg .x23).toNat + 32 * (64 + 64 * (groups + 1)) =
        (state.getReg .x22).toNat := by omega
    rw [show 1989 * (groups + 1 + 1) + fuel = 1988 + (1 + (1989 * (groups + 1) + fuel)) by omega,
      unrolled_group saltFetched prefixFetched tailFetched state messageBase
        (64 * (groups + 1)) current link,
      show 64 * (groups + 1 + 1) = 64 + 64 * (groups + 1) by omega, unrolled_leaves_add,
      show 5573 * (groups + 1 + 1) = 5573 + 5573 * (groups + 1) by omega,
      show 512 * (groups + 1 + 1) = 512 + 512 * (groups + 1) by omega]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    obtain ⟨middleInvariant, middleLink, middleWindow⟩ :=
      unrolled_leaves_progress 64 state (64 * (groups + 1)) current link currentWindow
        middle reached
    have again : BitVec.ult (middle.getReg .x23) (middle.getReg .x22) = true := by
      simp only [BitVec.ult, decide_eq_true_eq]
      omega
    rw [if_pos again, unrolled_loop_jump, ih middle middleInvariant middleLink middleWindow]
    simp [Execution.charge, Nat.add_assoc]
    simp only [show ∀ x : Nat, 5572 + (1 + x) = 5573 + x from fun x => by omega]

end CommitGolfCandidate
