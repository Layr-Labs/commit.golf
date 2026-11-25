import CommitGolfCandidate.Commit

/-! Execution of every 32-leaf iteration of the submitted commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem commit_position_run_support (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    ∃ chunks, chunks ∈ support (iterChunksFrom state 0 4) ∧
      finished = commitPositionNextState chunks := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨chunks, hc, rfl⟩ := reachable
  exact ⟨chunks, hc, rfl⟩

/-- The slot, salt and heap pointers advance by 32 leaves and the iteration counter drops.
The loop preserves the tree base, commitment pointer, stride `x29`, and constant call args. -/
theorem commit_position_registers (state finished : MachineState)
    (r29 : state.getReg .x29 = 2048)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x8 = state.getReg .x8 + 8192 ∧
    finished.getReg .x18 = state.getReg .x18 + 1024 ∧
    finished.getReg .x23 = state.getReg .x23 + 1536 ∧
    finished.getReg .x20 = state.getReg .x20 - 1 ∧
    finished.pc = (if state.getReg .x20 - 1 = 0 then 6844 else 4252) ∧
    ∀ reg ∈ [Reg.x9, .x26, .x29, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  obtain ⟨chunks, hc, rfl⟩ := commit_position_run_support state finished reachable
  have inner := iter_chunks_from_registers state chunks 0 4 (by decide) r29 hc
  have advance (current : MachineState) (reg : Reg) :
      (commitPositionNextState current).getReg reg =
        if reg = .x18 then current.getReg .x18 + 1024 else
        if reg = .x23 then current.getReg .x23 + 1536 else
        if reg = .x20 then current.getReg .x20 - 1 else current.getReg reg := by
    cases reg <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [advance]; simp only [reduceCtorEq, ↓reduceIte]; exact inner.1
  · rw [advance]; simp only [↓reduceIte]; rw [inner.2 .x18 (by decide) (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]
    rw [inner.2 .x23 (by decide) (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]
    rw [inner.2 .x20 (by decide) (by decide) (by decide) (by decide)]
  · change (if chunks.getReg .x20 - 1 = 0 then 6844 else 4252) = _
    rw [inner.2 .x20 (by decide) (by decide) (by decide) (by decide)]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [advance]; simp only [↓reduceIte, reduceCtorEq];
       exact inner.2 _ (by decide) (by decide) (by decide) (by decide))

/-- Safety and loop-control conditions, independent of the input bytes. `remaining`
counts the 32-leaf iterations still to be hashed. -/
structure CommitLeavesInvariant (state : MachineState) (remaining : Nat) : Prop where
  pc : state.pc = if remaining = 0 then 6844 else 4252
  counter : (state.getReg .x20).toNat = remaining
  bounded : remaining ≤ 2 ^ 19
  r29 : state.getReg .x29 = 2048
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  slotAligned : (state.getReg .x8).toNat % 8 = 0
  slotBound : (state.getReg .x8).toNat + 32 + 8192 * remaining ≤ MEMORY_BYTES
  salts : ∀ word < 128 * remaining,
    accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true
  heapAligned : (state.getReg .x23).toNat % 8 = 0
  heapBound : (state.getReg .x23).toNat + 1536 * remaining ≤ MEMORY_BYTES

theorem word_ofNat_toNat (word : Word) : word = BitVec.ofNat 64 word.toNat := by
  simp

theorem word_add_toNat (word : Word) (offset : Nat) (bound : word.toNat + offset ≤ MEMORY_BYTES) :
    (word + BitVec.ofNat 64 offset).toNat = word.toNat + offset := by
  have := pointer_offset_nat word.toNat offset bound
  rwa [← word_ofNat_toNat] at this

theorem slot_bound_now (s r M : Nat) (h : s + 32 + 8192 * (r + 1) ≤ M) : s + 8224 ≤ M := by
  have h1 : 8192 ≤ 8192 * (r + 1) := Nat.le_mul_of_pos_right 8192 (Nat.succ_pos r)
  have h2 : s + 8224 = s + 32 + 8192 := by omega
  rw [h2]
  exact Nat.le_trans (Nat.add_le_add_left h1 (s + 32)) h

theorem slot_bound_next (s r M : Nat) (h : s + 32 + 8192 * (r + 1) ≤ M) :
    s + 8192 + 32 + 8192 * r ≤ M := by
  have heq : s + 8192 + 32 + 8192 * r = s + 32 + 8192 * (r + 1) := by
    rw [Nat.mul_succ]; generalize 8192 * r = k; omega
  rwa [heq]

theorem slot_bound_step (s r M : Nat) (h : s + 32 + 8192 * (r + 1) ≤ M) : s + 8192 ≤ M := by
  have h1 := slot_bound_now s r M h
  exact Nat.le_trans (Nat.add_le_add_left (by decide : 8192 ≤ 8224) s) h1

theorem heap_bound_now (s r M : Nat) (h : s + 1536 * (r + 1) ≤ M) : s + 1536 ≤ M := by
  have h1 : 1536 ≤ 1536 * (r + 1) := Nat.le_mul_of_pos_right 1536 (Nat.succ_pos r)
  exact Nat.le_trans (Nat.add_le_add_left h1 s) h

theorem heap_bound_step (s r M : Nat) (h : s + 1536 * (r + 1) ≤ M) : s + 1536 ≤ M :=
  heap_bound_now s r M h

theorem heap_bound_next (s r M : Nat) (h : s + 1536 * (r + 1) ≤ M) : s + 1536 + 1536 * r ≤ M := by
  have heq : s + 1536 + 1536 * r = s + 1536 * (r + 1) := by
    rw [Nat.mul_succ]; generalize 1536 * r = k; omega
  rwa [heq]

theorem aligned_add (s k : Nat) (h : s % 8 = 0) (hk : k % 8 = 0) : (s + k) % 8 = 0 := by
  rw [Nat.add_mod, h, hk]

theorem counter_pred (word : Word) (remaining : Nat) (h : word.toNat = remaining + 1) :
    (word - 1).toNat = remaining := by
  have small : remaining + 1 < 2 ^ 64 := by rw [← h]; exact word.isLt
  rw [BitVec.toNat_sub]
  change (2 ^ 64 - 1 % 2 ^ 64 + word.toNat) % 2 ^ 64 = remaining
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
  have regs := commit_position_registers state finished invariant.r29 reachable
  have keep (reg : Reg) (member : reg ∈ [Reg.x9, .x26, .x29, .x5, .x11, .x13]) :=
    regs.2.2.2.2.2 reg member
  have slotNat : (state.getReg .x8 + 8192).toNat = (state.getReg .x8).toNat + 8192 :=
    word_add_toNat (state.getReg .x8) 8192 (slot_bound_step _ _ _ invariant.slotBound)
  have heapNat : (state.getReg .x23 + 1536).toNat = (state.getReg .x23).toNat + 1536 :=
    word_add_toNat (state.getReg .x23) 1536 (heap_bound_step _ _ _ invariant.heapBound)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.2.1]
    by_cases empty : remaining = 0
    · rw [if_pos ((counter_pred_zero _ remaining invariant.counter).mpr empty), if_pos empty]
    · rw [if_neg (fun h => empty ((counter_pred_zero _ remaining invariant.counter).mp h)), if_neg empty]
  · rw [regs.2.2.2.1]; exact counter_pred _ remaining invariant.counter
  · have := invariant.bounded; omega
  · exact (keep .x29 (by simp)).trans invariant.r29
  · exact (keep .x5 (by simp)).trans invariant.r5
  · exact (keep .x11 (by simp)).trans invariant.r11
  · exact (keep .x13 (by simp)).trans invariant.r13
  · rw [regs.1, slotNat]; exact aligned_add _ 8192 invariant.slotAligned (by decide)
  · rw [regs.1, slotNat]; exact slot_bound_next _ _ _ invariant.slotBound
  · intro word bounded
    rw [regs.2.1]
    have address : state.getReg .x18 + 1024 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x18 + BitVec.ofNat 64 (8 * (word + 128)) := by
      rw [show 8 * (word + 128) = 1024 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.salts (word + 128) (by omega)
  · rw [regs.2.2.1, heapNat]; exact aligned_add _ 1536 invariant.heapAligned (by decide)
  · rw [regs.2.2.1, heapNat]; exact heap_bound_next _ _ _ invariant.heapBound

/-- Loop state distribution, using precisely the same queries as the machine. -/
def commitLeaves : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← commitPositionRun state
      commitLeaves next remaining

attribute [local irreducible] execute commitPositionRun

/-- Every 32-leaf block is processed: 648 instructions, 1544 cycles and 128 queries
per iteration. -/
theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (648 * remaining + fuel) state true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (1544 * remaining) (128 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have pc : state.pc = 4252 := by simpa using invariant.pc
    have hstep : 648 * (remaining + 1) + fuel = 648 + (648 * remaining + fuel) := by
      rw [Nat.mul_succ, Nat.add_comm (648 * remaining) 648, Nat.add_assoc]
    rw [hstep,
      commit_position state pc invariant.r29 invariant.r5 invariant.r11 invariant.r13
        (state.getReg .x8).toNat (word_ofNat_toNat _) invariant.slotAligned
        (slot_bound_now _ _ _ invariant.slotBound)
        (fun word => invariant.salts word.val (by
          have hw := word.isLt
          have h1 : 128 ≤ 128 * (remaining + 1) := Nat.le_mul_of_pos_right 128 (Nat.succ_pos remaining)
          exact Nat.lt_of_lt_of_le hw h1))
        (state.getReg .x23).toNat (word_ofNat_toNat _) invariant.heapAligned
        (heap_bound_now _ _ _ invariant.heapBound)]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply bind_congr_of_forall_mem_support
    intro result _
    simp only [Execution.charge, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The leaf loop reaches the parent-building phase and preserves its pointers. -/
theorem commit_leaves_finished (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    finished.pc = 6844 ∧
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
      ((commit_position_registers state next invariant.r29 reached).2.2.2.2.2 reg (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))⟩

end CommitGolfCandidate
