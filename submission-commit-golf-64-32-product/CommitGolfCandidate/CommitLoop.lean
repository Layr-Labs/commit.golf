import CommitGolfCandidate.Commit

/-! Execution of every leaf iteration of the submitted commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-- The state after the eight in-place calls of one leaf, before the pointer advance. -/
def commitPositionInner (state : MachineState) (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 256) : MachineState :=
  (chainCallState (chainCallState (chainCallState (chainCallState (chainCallState (chainCallState (chainCallState (chainCallState (commitCopyState state 43) 0 a0) 1 a1) 2 a2) 3 a3) 4 a4) 5 a5) 6 a6) 7 a7)

theorem commit_position_run_support (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7, finished = commitPositionNextState (commitPositionInner state a0 a1 a2 a3 a4 a5 a6 a7) := by
  simp only [commitPositionRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨a0, _, a1, _, a2, _, a3, _, a4, _, a5, _, a6, _, a7, _, rfl⟩ := reachable
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩

theorem commit_position_inner_register (state : MachineState) (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 256)
    (reg : Reg) (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (commitPositionInner state a0 a1 a2 a3 a4 a5 a6 a7).getReg reg = state.getReg reg := by
  unfold commitPositionInner
  rw [chain_call_register _ 7 (by decide) _ reg n10 n12,
    chain_call_register _ 6 (by decide) _ reg n10 n12,
    chain_call_register _ 5 (by decide) _ reg n10 n12,
    chain_call_register _ 4 (by decide) _ reg n10 n12,
    chain_call_register _ 3 (by decide) _ reg n10 n12,
    chain_call_register _ 2 (by decide) _ reg n10 n12,
    chain_call_register _ 1 (by decide) _ reg n10 n12,
    chain_call_register _ 0 (by decide) _ reg n10 n12,
    commit_copy_register _ _ reg n6]

/-- The slot, salt, heap and index pointers advance. The loop preserves the tree
base, total leaf count, scratch pointer, commitment pointer and constant call
arguments. -/
theorem commit_position_registers (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x18 = state.getReg .x18 + 32 ∧
    finished.getReg .x23 = state.getReg .x23 + 32 ∧
    finished.getReg .x20 = state.getReg .x20 + 1 ∧
    finished.pc = (if BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) then 4268 else 4416) ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := commit_position_run_support state finished reachable
  have inner := commit_position_inner_register state a0 a1 a2 a3 a4 a5 a6 a7
  have advance (current : MachineState) (reg : Reg) :
      (commitPositionNextState current).getReg reg =
        if reg = .x8 then current.getReg .x8 + 256 else
        if reg = .x18 then current.getReg .x18 + 32 else
        if reg = .x23 then current.getReg .x23 + 32 else
        if reg = .x20 then current.getReg .x20 + 1 else current.getReg reg := by
    cases reg <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [advance]; simp only [↓reduceIte]; rw [inner .x8 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x18 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x23 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [↓reduceIte, reduceCtorEq]; rw [inner .x20 (by decide) (by decide) (by decide)]
  · change (if BitVec.ult ((commitPositionInner state a0 a1 a2 a3 a4 a5 a6 a7).getReg .x20 + 1)
        ((commitPositionInner state a0 a1 a2 a3 a4 a5 a6 a7).getReg .x19) then 4268 else 4416) = _
    rw [inner .x20 (by decide) (by decide) (by decide), inner .x19 (by decide) (by decide) (by decide)]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [advance]; simp only [↓reduceIte, reduceCtorEq];
       exact inner _ (by decide) (by decide) (by decide))

/-- Safety and loop-control conditions, independent of the input bytes. -/
structure CommitLeavesInvariant (state : MachineState) (remaining : Nat) : Prop where
  pc : state.pc = if remaining = 0 then 4416 else 4268
  counter : (state.getReg .x20).toNat + remaining = (state.getReg .x19).toNat
  bounded : (state.getReg .x19).toNat ≤ 2 ^ 24
  scratch : state.getReg .x21 = 256
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 64
  r13 : state.getReg .x13 = 0
  slotAligned : (state.getReg .x8).toNat % 8 = 0
  slotBound : (state.getReg .x8).toNat + 32 + 256 * remaining ≤ MEMORY_BYTES
  salts : ∀ word < 4 * remaining,
    accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true
  heapAligned : (state.getReg .x23).toNat % 8 = 0
  heapBound : (state.getReg .x23).toNat + 32 * remaining ≤ MEMORY_BYTES

theorem word_ofNat_toNat (word : Word) : word = BitVec.ofNat 64 word.toNat := by
  simp

theorem word_add_toNat (word : Word) (offset : Nat) (bound : word.toNat + offset ≤ MEMORY_BYTES) :
    (word + BitVec.ofNat 64 offset).toNat = word.toNat + offset := by
  have := pointer_offset_nat word.toNat offset bound
  rwa [← word_ofNat_toNat] at this

set_option maxRecDepth 20000 in
theorem slot_bound_now (s r M : Nat) (h : s + 32 + 256 * (r + 1) ≤ M) : s + 288 ≤ M := by omega
theorem slot_bound_next (s r M : Nat) (h : s + 32 + 256 * (r + 1) ≤ M) :
    s + 256 + 32 + 256 * r ≤ M := by omega
set_option maxRecDepth 20000 in
theorem slot_bound_step (s r M : Nat) (h : s + 32 + 256 * (r + 1) ≤ M) : s + 256 ≤ M := by omega
theorem heap_bound_now (s r M : Nat) (h : s + 32 * (r + 1) ≤ M) : s + 32 ≤ M := by omega
theorem heap_bound_next (s r M : Nat) (h : s + 32 * (r + 1) ≤ M) : s + 32 + 32 * r ≤ M := by omega
theorem aligned_add (s k : Nat) (h : s % 8 = 0) (hk : k % 8 = 0) : (s + k) % 8 = 0 := by omega

theorem commit_leaves_next_invariant (state finished : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + 1))
    (reachable : finished ∈ support (commitPositionRun state)) :
    CommitLeavesInvariant finished remaining := by
  have regs := commit_position_registers state finished reachable
  have keep (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x21, .x26, .x5, .x11, .x13]) :=
    regs.2.2.2.2.2 reg member
  have counter : (state.getReg .x20 + 1).toNat = (state.getReg .x20).toNat + 1 := by
    rw [BitVec.toNat_add]
    change ((state.getReg .x20).toNat + 1) % 18446744073709551616 = _
    apply Nat.mod_eq_of_lt
    have := invariant.counter
    have := invariant.bounded
    omega
  have branch : BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) =
      decide (0 < remaining) := by
    simp only [BitVec.ult, counter]
    have equivalent : (state.getReg .x20).toNat + 1 < (state.getReg .x19).toNat ↔ 0 < remaining := by
      have := invariant.counter
      omega
    simp only [equivalent]
  have slotNat : (state.getReg .x8 + 256).toNat = (state.getReg .x8).toNat + 256 :=
    word_add_toNat (state.getReg .x8) 256
      (slot_bound_step _ _ _ invariant.slotBound)
  have heapNat : (state.getReg .x23 + 32).toNat = (state.getReg .x23).toNat + 32 :=
    word_add_toNat (state.getReg .x23) 32 (heap_bound_now _ _ _ invariant.heapBound)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.2.1, branch]
    by_cases empty : remaining = 0 <;> simp [empty, Nat.pos_of_ne_zero]
  · rw [regs.2.2.2.1, keep .x19 (by simp), counter]
    have := invariant.counter
    omega
  · rw [keep .x19 (by simp)]
    exact invariant.bounded
  · exact (keep .x21 (by simp)).trans invariant.scratch
  · exact (keep .x5 (by simp)).trans invariant.r5
  · exact (keep .x11 (by simp)).trans invariant.r11
  · exact (keep .x13 (by simp)).trans invariant.r13
  · rw [regs.1, slotNat]; exact aligned_add _ 256 invariant.slotAligned (by decide)
  · rw [regs.1, slotNat]; exact slot_bound_next _ _ _ invariant.slotBound
  · intro word bounded
    rw [regs.2.1]
    have address : state.getReg .x18 + 32 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x18 + BitVec.ofNat 64 (8 * (word + 4)) := by
      rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.salts (word + 4) (by omega)
  · rw [regs.2.2.1, heapNat]; exact aligned_add _ 32 invariant.heapAligned (by decide)
  · rw [regs.2.2.1, heapNat]; exact heap_bound_next _ _ _ invariant.heapBound

/-- Loop state distribution, using precisely the same queries as the machine. -/
def commitLeaves : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← commitPositionRun state
      commitLeaves next remaining

attribute [local irreducible] execute commitPositionRun

/-- Every leaf is processed. This is an exact execution equality, not a sampled
benchmark: 37 instructions, 93 cycles and four queries per leaf. -/
theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (37 * remaining + fuel) state true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (93 * remaining) (8 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have pc : state.pc = 4268 := by simpa using invariant.pc
    rw [show 37 * (remaining + 1) + fuel = 37 + (37 * remaining + fuel) by omega,
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
    finished.pc = 4416 ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26], finished.getReg reg = state.getReg reg := by
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
