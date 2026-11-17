import CommitGolfCandidate.UnrollLeaf
import CommitGolfCandidate.ContiguousEntry

/-! Sixty-four relocated leaf bodies share one loop branch. Each body is the
contiguous leaf without its per-leaf branch: 33 instructions and 89 cycles. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- One relocated position: 33 instructions, 89 cycles, eight queries. -/
theorem unroll_position (image : Image) (B : Nat) (fetched : UnrollBodyFetched image B)
    (state : MachineState) (messageBase : Word) (pc : state.pc = 4280)
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
    execute image (33 + fuel) (cursorNormalize state messageBase (BitVec.ofNat 64 B)) true =
      (do let finished ← commitPositionRun state
          let result ← execute image fuel
            (cursorNormalize finished messageBase (BitVec.ofNat 64 (B + 132))) true
          return result.charge 89 8) := by
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
      accessValid ((cursorNormalize state messageBase (BitVec.ofNat 64 B)).getReg .x10 +
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
      accessValid ((cursorNormalize state messageBase (BitVec.ofNat 64 B)).getReg .x18 +
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
  have leafRun := unroll_leaf_blocks image B fetched.pre fetched.tail
    ((cursorLeafFrame ready messageBase).setPC (BitVec.ofNat 64 (B + 28))) cursor rfl
    (by rw [MachineState.getReg_setPC, cursor_frame_pointer]; exact readyChain)
    (by simpa only [StreamingOracleReady, MachineState.getReg_setPC] using readyOracle)
    (by dsimp [cursor]; omega) (by dsimp [cursor]; omega)
    (by simpa only [MachineState.getReg_setPC] using readyHeap) (2 + fuel) true
  rw [show 33 + fuel = 7 + (24 + (2 + fuel)) by omega,
    unroll_salt_execute _ B fetched.salt _ rfl physicalSalt destinationValid,
    unroll_salt_ready state messageBase B link, leafRun]
  rw [contiguous_heap_pc_bind (cursorLeafFrame ready messageBase) cursor
    (BitVec.ofNat 64 (B + 28)) (BitVec.ofNat 64 (B + 124))
    (fun finished => do
      let result ← execute image (2 + fuel) finished true
      return result.charge 80 8)]
  rw [fused_leaf_reference_bind ready
    cursor (readySource.trans source) readyChain
    (by
      change (ready.getReg .x8).toNat - 32 = cursor
      rw [readySource]) messageBase (BitVec.ofNat 64 (B + 124))
    (fun finished => do
      let result ← execute image (2 + fuel) finished true
      return result.charge 80 8)]
  simp only [commitPositionRun, commitLeafReadyState, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  rw [unroll_latch_execute _ B fetched.tail (cursorNormalize leaf messageBase (BitVec.ofNat 64 (B + 124))) rfl,
    unroll_latch_frame, cursor_next_frame_pc]
  simp [Execution.charge, ← Nat.add_assoc]

theorem commit_leaves_add (state : MachineState) (a b : Nat) :
    commitLeaves state (a + b) = (do let middle ← commitLeaves state a; commitLeaves middle b) := by
  induction a generalizing state with
  | zero => simp [commitLeaves]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [commitLeaves, ih, bind_assoc]

/-- Facts carried through any number of reference positions. -/
theorem unroll_leaves_support (state : MachineState) (k remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + k))
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * (remaining + k) = (state.getReg .x22).toNat)
    (finished : MachineState) (reached : finished ∈ support (commitLeaves state k)) :
    CommitLeavesInvariant finished remaining ∧ finished.getReg .x1 = 4316 ∧
      (finished.getReg .x23).toNat + 32 * remaining = (finished.getReg .x22).toNat := by
  induction k generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reached
    subst finished
    exact ⟨invariant, link, window⟩
  | succ k ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reached
    obtain ⟨next, nextReached, rest⟩ := reached
    have inv' : CommitLeavesInvariant state ((remaining + k) + 1) := by
      simpa only [show remaining + (k + 1) = (remaining + k) + 1 by omega] using invariant
    have window' : (state.getReg .x23).toNat + 32 * ((remaining + k) + 1) =
        (state.getReg .x22).toNat := by
      simpa only [show remaining + (k + 1) = (remaining + k) + 1 by omega] using window
    exact ih next (commit_leaves_next_invariant state next (remaining + k) inv' nextReached)
      (contiguous_position_link state next nextReached)
      (outer_heap_progress_next state next (remaining + k) window' nextReached) rest

/-- k consecutive relocated bodies. -/
theorem unroll_bodies (image : Image) (B k : Nat)
    (fetched : ∀ j < k, UnrollBodyFetched image (B + 132 * j))
    (state : MachineState) (messageBase : Word) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + k))
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * (remaining + k) = (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute image (33 * k + fuel) (cursorNormalize state messageBase (BitVec.ofNat 64 B)) true =
      (do let finished ← commitLeaves state k
          let result ← execute image fuel
            (cursorNormalize finished messageBase (BitVec.ofNat 64 (B + 132 * k))) true
          return result.charge (89 * k) (8 * k)) := by
  induction k generalizing state B with
  | zero => simp [commitLeaves, Execution.charge]
  | succ k ih =>
    have inv' : CommitLeavesInvariant state ((remaining + k) + 1) := by
      simpa only [show remaining + (k + 1) = (remaining + k) + 1 by omega] using invariant
    have window' : (state.getReg .x23).toNat + 32 * ((remaining + k) + 1) =
        (state.getReg .x22).toNat := by
      simpa only [show remaining + (k + 1) = (remaining + k) + 1 by omega] using window
    have pc : state.pc = 4280 := by simpa using inv'.pc
    rw [show 33 * (k + 1) + fuel = 33 + (33 * k + fuel) by omega,
      unroll_position image B (by simpa using fetched 0 (by omega)) state messageBase pc link
        inv'.scratch inv'.sourceAbove inv'.oracleReady
        (fun word => inv'.salts word.val (by omega))
        (fun word => inv'.heap word.val (by omega))
        (fun word bound => inv'.message word (by omega))]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    have nextFetched : ∀ j < k, UnrollBodyFetched image ((B + 132) + 132 * j) := by
      intro j hj
      have := fetched (j + 1) (by omega)
      rwa [show B + 132 * (j + 1) = (B + 132) + 132 * j by omega] at this
    rw [ih (B + 132) nextFetched next
      (commit_leaves_next_invariant state next (remaining + k) inv' reached)
      (contiguous_position_link state next reached)
      (outer_heap_progress_next state next (remaining + k) window' reached),
      show B + 132 + 132 * k = B + 132 * (k + 1) by omega]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Group end at 1019852: branch to the re-entry jump while heap remains, else exit jump. -/
def UnrollEndFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 1019852 → fetch image state = some (.base (.BLTU .x23 .x22 8))) ∧
    (state.pc = 1019856 → fetch image state = some (.base (.JAL .x0 1081888))) ∧
    (state.pc = 1019860 → fetch image state = some (.base (.JAL .x0 2088696)))

theorem unroll_end_branch (state : MachineState) (pc : state.pc = 1019852) :
    ordinaryStep state (.base (.BLTU .x23 .x22 8)) =
      some (state.setPC (if BitVec.ult (state.getReg .x23) (state.getReg .x22)
        then 1019860 else 1019856)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, pc,
    MachineState.setPC]
  split <;> simp_all

theorem unroll_exit_jump (state : MachineState) (pc : state.pc = 1019856) :
    ordinaryStep state (.base (.JAL .x0 1081888)) = some (state.setPC 4592) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc,
    MachineState.setPC, MachineState.setReg]

theorem unroll_loop_jump (state : MachineState) (pc : state.pc = 1019860) :
    ordinaryStep state (.base (.JAL .x0 2088696)) = some (state.setPC 1011404) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc,
    MachineState.setPC, MachineState.setReg]

/-- The complete unrolled leaf loop: 2114 instructions and 5698 cycles per 64 leaves. -/
theorem unroll_leaves (image : Image)
    (bodies : ∀ j < 64, UnrollBodyFetched image (1011404 + 132 * j))
    (ending : UnrollEndFetched image)
    (state : MachineState) (messageBase : Word) (groups : Nat) (positive : 0 < groups)
    (invariant : CommitLeavesInvariant state (64 * groups))
    (link : state.getReg .x1 = 4316)
    (window : (state.getReg .x23).toNat + 32 * (64 * groups) = (state.getReg .x22).toNat)
    (fuel : Nat) :
    execute image (2114 * groups + fuel) (cursorNormalize state messageBase 1011404) true =
      (do let finished ← commitLeaves state (64 * groups)
          let result ← execute image fuel (cursorNormalize finished messageBase 4592) true
          return result.charge (5698 * groups) (512 * groups)) := by
  induction groups generalizing state with
  | zero => omega
  | succ groups ih =>
    have inv' : CommitLeavesInvariant state (64 * groups + 64) := by
      simpa only [show 64 * (groups + 1) = 64 * groups + 64 by omega] using invariant
    have window' : (state.getReg .x23).toNat + 32 * (64 * groups + 64) = (state.getReg .x22).toNat := by
      simpa only [show 64 * (groups + 1) = 64 * groups + 64 by omega] using window
    have run := unroll_bodies image 1011404 64 bodies state messageBase (64 * groups) inv' link window'
    rw [show 2114 * (groups + 1) + fuel = 33 * 64 + (2 + (2114 * groups + fuel)) by omega,
      show (1011404 : Word) = BitVec.ofNat 64 1011404 from rfl, run]
    rw [show 64 * (groups + 1) = 64 + 64 * groups by omega, commit_leaves_add]
    simp only [bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    obtain ⟨midInv, midLink, midWindow⟩ :=
      unroll_leaves_support state 64 (64 * groups) inv' link window' middle reached
    let atEnd := cursorNormalize middle messageBase (BitVec.ofNat 64 (1011404 + 132 * 64))
    have endPC : atEnd.pc = 1019852 := rfl
    have heapReg : atEnd.getReg .x23 = middle.getReg .x23 :=
      cursor_frame_register middle messageBase .x23 (by decide)
    have endReg : atEnd.getReg .x22 = middle.getReg .x22 :=
      cursor_frame_register middle messageBase .x22 (by decide)
    have branch : BitVec.ult (atEnd.getReg .x23) (atEnd.getReg .x22) = decide (0 < groups) := by
      rw [heapReg, endReg]
      simp only [BitVec.ult, decide_eq_decide]
      omega
    rw [show 2 + (2114 * groups + fuel) = ((2114 * groups + fuel) + 1) + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ ((ending atEnd).1 endPC) (unroll_end_branch atEnd endPC),
      branch]
    by_cases more : 0 < groups
    · simp only [more, decide_true, ite_true]
      rw [execute_ordinary_step _ _ _ _ _ _ ((ending _).2.2 rfl) (unroll_loop_jump _ rfl)]
      have restart : (atEnd.setPC 1019860).setPC 1011404 = cursorNormalize middle messageBase 1011404 := rfl
      rw [restart, ih middle more midInv midLink midWindow]
      simp [Execution.charge, instructionCycles, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      simp only [show ∀ x : Nat, 1 + (1 + (5696 + x)) = 5698 + x from fun x => by omega]
    · have zero : groups = 0 := by omega
      subst zero
      simp only [lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
      rw [show 2114 * 0 + fuel + 1 = fuel + 1 by omega, execute_ordinary_step _ _ _ _ _ _ ((ending _).2.1 rfl) (unroll_exit_jump _ rfl)]
      have exitState : (atEnd.setPC 1019856).setPC 4592 = cursorNormalize middle messageBase 4592 := rfl
      rw [exitState]
      simp [commitLeaves, Execution.charge, instructionCycles, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
