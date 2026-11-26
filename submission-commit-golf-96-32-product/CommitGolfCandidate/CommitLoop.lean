import CommitGolfCandidate.Commit

/-! Execution of every pair iteration of the submitted commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem commit_position_run_support (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    ∃ first second, first ∈ support (laneRun (commitSaltState state 0) 0) ∧
      second ∈ support (laneRun (commitSaltState first 1) 1) ∧
      finished = commitPositionNextState second := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨first, hf, second, hs, rfl⟩ := reachable
  exact ⟨first, second, hf, hs, rfl⟩

/-- Registers untouched by the two lanes and the two salt copies. -/
theorem commit_position_inner_register (state first second : MachineState)
    (hf : first ∈ support (laneRun (commitSaltState state 0) 0))
    (hs : second ∈ support (laneRun (commitSaltState first 1) 1))
    (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    second.getReg reg = state.getReg reg := by
  rw [lane_run_register _ second 1 (by decide) hs reg n10 n12, commit_salt_register _ _ reg n6,
    lane_run_register _ first 0 (by decide) hf reg n10 n12, commit_salt_register _ _ reg n6]

/-- The slot, salt and heap pointers advance by one pair and the pair counter drops.
The loop preserves the tree base, commitment pointer and constant call arguments. -/
theorem commit_position_registers (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x8 = state.getReg .x8 + 512 ∧
    finished.getReg .x18 = state.getReg .x18 + 48 ∧
    finished.getReg .x23 = state.getReg .x23 + 96 ∧
    finished.getReg .x20 = state.getReg .x20 - 1 ∧
    finished.pc = (if state.getReg .x20 - 1 = 0 then 4424 else 4252) ∧
    ∀ reg ∈ [Reg.x9, .x26, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  obtain ⟨first, second, hf, hs, rfl⟩ := commit_position_run_support state finished reachable
  have inner := commit_position_inner_register state first second hf hs
  have advance (current : MachineState) (reg : Reg) :
      (commitPositionNextState current).getReg reg =
        if reg = .x8 then current.getReg .x8 + 512 else
        if reg = .x18 then current.getReg .x18 + 48 else
        if reg = .x23 then current.getReg .x23 + 96 else
        if reg = .x20 then current.getReg .x20 - 1 else current.getReg reg := by
    cases reg <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [advance]; simp only [↓reduceIte]; rw [inner .x8 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x18 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x23 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x20 (by decide) (by decide) (by decide)]
  · change (if second.getReg .x20 - 1 = 0 then 4424 else 4252) = _
    rw [inner .x20 (by decide) (by decide) (by decide)]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      (rw [advance]; simp only [↓reduceIte, reduceCtorEq];
       exact inner _ (by decide) (by decide) (by decide))

/-- Safety and loop-control conditions, independent of the input bytes. `remaining`
counts the pairs still to be hashed. -/
structure CommitLeavesInvariant (state : MachineState) (remaining : Nat) : Prop where
  pc : state.pc = if remaining = 0 then 4424 else 4252
  counter : (state.getReg .x20).toNat = remaining
  bounded : remaining ≤ 2 ^ 23
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  slotAligned : (state.getReg .x8).toNat % 8 = 0
  slotBound : (state.getReg .x8).toNat + 32 + 512 * remaining ≤ MEMORY_BYTES
  salts : ∀ word < 6 * remaining,
    accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true
  heapAligned : (state.getReg .x23).toNat % 8 = 0
  heapBound : (state.getReg .x23).toNat + 96 * remaining ≤ MEMORY_BYTES

theorem word_ofNat_toNat (word : Word) : word = BitVec.ofNat 64 word.toNat := by
  simp

theorem word_add_toNat (word : Word) (offset : Nat) (bound : word.toNat + offset ≤ MEMORY_BYTES) :
    (word + BitVec.ofNat 64 offset).toNat = word.toNat + offset := by
  have := pointer_offset_nat word.toNat offset bound
  rwa [← word_ofNat_toNat] at this

set_option maxRecDepth 20000 in
theorem slot_bound_now (s r M : Nat) (h : s + 32 + 512 * (r + 1) ≤ M) : s + 544 ≤ M := by omega
set_option maxRecDepth 20000 in
theorem slot_bound_next (s r M : Nat) (h : s + 32 + 512 * (r + 1) ≤ M) :
    s + 512 + 32 + 512 * r ≤ M := by omega
set_option maxRecDepth 20000 in
theorem slot_bound_step (s r M : Nat) (h : s + 32 + 512 * (r + 1) ≤ M) : s + 512 ≤ M := by omega
theorem heap_bound_now (s r M : Nat) (h : s + 96 * (r + 1) ≤ M) : s + 64 ≤ M := by omega
theorem heap_bound_step (s r M : Nat) (h : s + 96 * (r + 1) ≤ M) : s + 96 ≤ M := by omega
theorem heap_bound_next (s r M : Nat) (h : s + 96 * (r + 1) ≤ M) : s + 96 + 96 * r ≤ M := by omega
theorem aligned_add (s k : Nat) (h : s % 8 = 0) (hk : k % 8 = 0) : (s + k) % 8 = 0 := by omega

theorem counter_pred (word : Word) (remaining : Nat) (h : word.toNat = remaining + 1) :
    (word - 1).toNat = remaining := by
  have small : remaining + 1 < 2^64 := by rw [← h]; exact word.isLt
  rw [BitVec.toNat_sub]
  change (2^64 - 1 % 2^64 + word.toNat) % 2^64 = remaining
  rw [h]
  omega

theorem counter_pred_zero (word : Word) (remaining : Nat) (h : word.toNat = remaining + 1) :
    (word - 1 = 0) ↔ remaining = 0 := by
  constructor
  · intro zero
    have := congrArg BitVec.toNat zero
    rw [counter_pred word remaining h] at this
    simpa using this
  · intro zero
    apply BitVec.eq_of_toNat_eq
    rw [counter_pred word remaining h, zero]
    rfl

theorem commit_leaves_next_invariant (state finished : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + 1))
    (reachable : finished ∈ support (commitPositionRun state)) :
    CommitLeavesInvariant finished remaining := by
  have regs := commit_position_registers state finished reachable
  have keep (reg : Reg) (member : reg ∈ [Reg.x9, .x26, .x5, .x11, .x13]) :=
    regs.2.2.2.2.2 reg member
  have slotNat : (state.getReg .x8 + 512).toNat = (state.getReg .x8).toNat + 512 :=
    word_add_toNat (state.getReg .x8) 512
      (slot_bound_step _ _ _ invariant.slotBound)
  have heapNat : (state.getReg .x23 + 96).toNat = (state.getReg .x23).toNat + 96 :=
    word_add_toNat (state.getReg .x23) 96 (heap_bound_step _ _ _ invariant.heapBound)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.2.1]
    by_cases empty : remaining = 0
    · rw [if_pos ((counter_pred_zero _ remaining invariant.counter).mpr empty), if_pos empty]
    · rw [if_neg (fun h => empty ((counter_pred_zero _ remaining invariant.counter).mp h)), if_neg empty]
  · rw [regs.2.2.2.1]; exact counter_pred _ remaining invariant.counter
  · have := invariant.bounded; omega
  · exact (keep .x5 (by simp)).trans invariant.r5
  · exact (keep .x11 (by simp)).trans invariant.r11
  · exact (keep .x13 (by simp)).trans invariant.r13
  · rw [regs.1, slotNat]; exact aligned_add _ 512 invariant.slotAligned (by decide)
  · rw [regs.1, slotNat]; exact slot_bound_next _ _ _ invariant.slotBound
  · intro word bounded
    rw [regs.2.1]
    have address : state.getReg .x18 + 48 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x18 + BitVec.ofNat 64 (8 * (word + 6)) := by
      rw [show 8 * (word + 6) = 48 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.salts (word + 6) (by omega)
  · rw [regs.2.2.1, heapNat]; exact aligned_add _ 96 invariant.heapAligned (by decide)
  · rw [regs.2.2.1, heapNat]; exact heap_bound_next _ _ _ invariant.heapBound

/-- Loop state distribution, using precisely the same queries as the machine. -/
def commitLeaves : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← commitPositionRun state
      commitLeaves next remaining

attribute [local irreducible] execute commitPositionRun

/-- Every pair is processed. This is an exact execution equality, not a sampled
benchmark: 43 instructions, 99 cycles and eight queries per pair. -/
theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (43 * remaining + fuel) state true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (99 * remaining) (8 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have pc : state.pc = 4252 := by simpa using invariant.pc
    rw [show 43 * (remaining + 1) + fuel = 43 + (43 * remaining + fuel) by omega,
      commit_position state pc invariant.r5 invariant.r11 invariant.r13
        (state.getReg .x8).toNat (word_ofNat_toNat _) invariant.slotAligned
        (slot_bound_now _ _ _ invariant.slotBound)
        (fun word => invariant.salts word.val (by omega))
        (state.getReg .x23).toNat (word_ofNat_toNat _) invariant.heapAligned
        (heap_bound_now _ _ _ invariant.heapBound)]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

/-- The leaf loop reaches the parent-building phase and preserves its pointers. -/
theorem commit_leaves_finished (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    finished.pc = 4424 ∧
    ∀ reg ∈ [Reg.x9, .x26, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simpa using invariant.pc, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (commit_leaves_next_invariant state next remaining invariant reached) rest
    exact ⟨done.1, fun reg member => (done.2 reg member).trans
      ((commit_position_registers state next reached).2.2.2.2.2 reg (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))⟩

end CommitGolfCandidate
