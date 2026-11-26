import CommitGolfCandidate.Commit

/-! Execution of every 32-leaf block iteration of the submitted commitment image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

theorem commit_block_run_support (state finished : MachineState)
    (reachable : finished ∈ support (commitBlockRun state)) :
    ∃ hashed, hashed ∈ support (leafBlockLanes state 0 32) ∧
      finished = commitBlockNextState hashed := by
  simp only [commitBlockRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨hashed, hh, rfl⟩ := reachable
  exact ⟨hashed, hh, rfl⟩

attribute [local irreducible] commitBlockRun

/-- The slot, salt and heap pointers advance by one 32-leaf block (8192, 512, 1536).
The loop preserves the tree base, salt end sentinel, commitment pointer and constant call args. -/
theorem commit_block_registers (state finished : MachineState)
    (reachable : finished ∈ support (commitBlockRun state)) :
    finished.getReg .x10 = state.getReg .x10 + 8192 ∧
    finished.getReg .x18 = state.getReg .x18 + 512 ∧
    finished.getReg .x23 = state.getReg .x23 + 1536 ∧
    finished.pc = (if state.getReg .x18 + 512 = state.getReg .x20 then 6420 else 4232) ∧
    ∀ reg ∈ [Reg.x9, .x20, .x26, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  obtain ⟨hashed, hh, rfl⟩ := commit_block_run_support state finished reachable
  have inner := leaf_block_lanes_registers state hashed 0 32 hh
  have advance (current : MachineState) (reg : Reg) :
      (commitBlockNextState current).getReg reg =
        if reg = .x18 then current.getReg .x18 + 512 else
        if reg = .x23 then current.getReg .x23 + 1536 else current.getReg reg := by
    cases reg <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [advance]; simp only [reduceCtorEq, ↓reduceIte]; exact inner.1
  · rw [advance]; simp only [↓reduceIte]; rw [inner.2.2 .x18 (by decide) (by decide) (by decide)]
  · rw [advance]; simp only [reduceCtorEq, ↓reduceIte]; rw [inner.2.2 .x23 (by decide) (by decide) (by decide)]
  · unfold commitBlockNextState
    simp only [MachineState.setPC]
    rw [inner.2.2 .x18 (by decide) (by decide) (by decide),
      inner.2.2 .x20 (by decide) (by decide) (by decide)]
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [advance]; simp only [reduceCtorEq, ↓reduceIte];
       exact inner.2.2 _ (by decide) (by decide) (by decide))

/-- Safety and loop-control conditions for the 32-leaf block loop. `remaining`
counts the 32-leaf blocks still to be hashed (`≤ 2^19 = 524,288`). -/
structure CommitLeavesInvariant (state : MachineState) (remaining : Nat) : Prop where
  pc : state.pc = if remaining = 0 then 6420 else 4232
  saltEnd : state.getReg .x20 = state.getReg .x18 + BitVec.ofNat 64 (512 * remaining)
  bounded : remaining ≤ 2 ^ 19
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  slotAligned : (state.getReg .x10).toNat % 8 = 0
  slotBound : (state.getReg .x10).toNat + 24 + 8192 * remaining ≤ MEMORY_BYTES
  saltBound : (state.getReg .x18).toNat + 512 * remaining ≤ MEMORY_BYTES
  saltAligned : (state.getReg .x18).toNat % 8 = 0
  heapAligned : (state.getReg .x23).toNat % 8 = 0
  heapBound : (state.getReg .x23).toNat + 1536 * remaining ≤ MEMORY_BYTES

theorem word_ofNat_toNat (word : Word) : word = BitVec.ofNat 64 word.toNat := by
  simp

theorem word_add_toNat (word : Word) (offset : Nat) (bound : word.toNat + offset ≤ MEMORY_BYTES) :
    (word + BitVec.ofNat 64 offset).toNat = word.toNat + offset := by
  have := pointer_offset_nat word.toNat offset bound
  rwa [← word_ofNat_toNat] at this

theorem aligned_add (s k : Nat) (h : s % 8 = 0) (hk : k % 8 = 0) : (s + k) % 8 = 0 := by omega

theorem commit_leaves_next_invariant (state finished : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state (remaining + 1))
    (reachable : finished ∈ support (commitBlockRun state)) :
    CommitLeavesInvariant finished remaining := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have regs := commit_block_registers state finished reachable
  have keep (reg : Reg) (member : reg ∈ [Reg.x9, .x20, .x26, .x5, .x11, .x13]) :=
    regs.2.2.2.2 reg member
  have hslotB := invariant.slotBound
  have hsaltB := invariant.saltBound
  have hheapB := invariant.heapBound
  have slotNat : (state.getReg .x10 + 8192).toNat = (state.getReg .x10).toNat + 8192 :=
    word_add_toNat (state.getReg .x10) 8192 (Nat.le_trans (by clear * -; omega) hslotB)
  have saltNat : (state.getReg .x18 + 512).toNat = (state.getReg .x18).toNat + 512 :=
    word_add_toNat (state.getReg .x18) 512 (Nat.le_trans (by clear * -; omega) hsaltB)
  have heapNat : (state.getReg .x23 + 1536).toNat = (state.getReg .x23).toNat + 1536 :=
    word_add_toNat (state.getReg .x23) 1536 (Nat.le_trans (by clear * -; omega) hheapB)
  have hEnd : state.getReg .x20 = state.getReg .x18 + 512 + BitVec.ofNat 64 (512 * remaining) := by
    rw [invariant.saltEnd, BitVec.add_assoc]
    change _ = state.getReg .x18 + (BitVec.ofNat 64 512 + BitVec.ofNat 64 (512 * remaining))
    rw [← BitVec.ofNat_add]
    exact congrArg (fun n => state.getReg .x18 + BitVec.ofNat 64 n) (by clear * -; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs.2.2.2.1, hEnd]
    by_cases empty : remaining = 0
    · subst remaining; simp
    · have neq : state.getReg .x18 + 512 ≠
          state.getReg .x18 + 512 + BitVec.ofNat 64 (512 * remaining) := by
        intro same
        have hnat := congrArg BitVec.toNat same
        have boundRem : (state.getReg .x18 + 512).toNat + 512 * remaining ≤ MEMORY_BYTES := by
          rw [saltNat]; exact Nat.le_trans (by clear * -; omega) hsaltB
        rw [word_add_toNat _ (512 * remaining) boundRem] at hnat
        clear * - hnat empty; omega
      rw [if_neg neq, if_neg empty]
  · rw [keep .x20 (by simp), regs.2.1]; exact hEnd
  · have hb := invariant.bounded; clear * - hb; omega
  · exact (keep .x5 (by simp)).trans invariant.r5
  · exact (keep .x11 (by simp)).trans invariant.r11
  · exact (keep .x13 (by simp)).trans invariant.r13
  · rw [regs.1, slotNat]; exact aligned_add _ 8192 invariant.slotAligned (by decide)
  · rw [regs.1, slotNat]; exact Nat.le_trans (by clear * -; omega) hslotB
  · rw [regs.2.1, saltNat]; exact Nat.le_trans (by clear * -; omega) hsaltB
  · rw [regs.2.1, saltNat]; exact aligned_add _ 512 invariant.saltAligned (by decide)
  · rw [regs.2.2.1, heapNat]; exact aligned_add _ 1536 invariant.heapAligned (by decide)
  · rw [regs.2.2.1, heapNat]; exact Nat.le_trans (by clear * -; omega) hheapB

/-- Loop state distribution over `remaining` 32-leaf blocks. -/
def commitLeaves : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← commitBlockRun state
      commitLeaves next remaining

attribute [local irreducible] execute

/-- Every 32-leaf block is processed: 547 instructions, 1,443 cycles, 128 queries per block. -/
theorem commit_leaves (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (fuel : Nat) :
    execute (submission.image .commit) (547 * remaining + fuel) state true =
      (do let finished ← commitLeaves state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (1443 * remaining) (128 * remaining)) := by
  induction remaining generalizing state with
  | zero => simp [commitLeaves, Execution.charge]
  | succ remaining ih =>
    have mem : MEMORY_BYTES = 2^36 := rfl
    have pc : state.pc = 4232 := by simpa using invariant.pc
    have hslotB := invariant.slotBound
    have hsaltB := invariant.saltBound
    have hsaltA := invariant.saltAligned
    have hheapB := invariant.heapBound
    have saltValid : ∀ word < 64,
        accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      intro word hw
      have hwb : (state.getReg .x18).toNat + 8 * word ≤ MEMORY_BYTES :=
        Nat.le_trans (by clear * - hw; omega) hsaltB
      simp only [accessValid, rangeValid, word_add_toNat _ (8 * word) hwb,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact Nat.le_trans (by clear * - hw; omega) hsaltB
      · clear * - hsaltA; omega
    have hstep := commit_block state pc invariant.r5 invariant.r11 invariant.r13
      (state.getReg .x10).toNat (word_ofNat_toNat _) invariant.slotAligned
      (Nat.le_trans (by clear * -; omega) hslotB) saltValid
      (state.getReg .x23).toNat (word_ofNat_toNat _) invariant.heapAligned
      (Nat.le_trans (by clear * -; omega) hheapB) (547 * remaining + fuel)
    rw [show 547 * (remaining + 1) + fuel = 547 + (547 * remaining + fuel) by clear * -; omega,
      hstep]
    simp only [commitLeaves, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (commit_leaves_next_invariant state next remaining invariant reached)]
    simp only [bind_assoc, pure_bind, charge_charge,
      show 1443 + 1443 * remaining = 1443 * (remaining + 1) by omega,
      show 128 + 128 * remaining = 128 * (remaining + 1) by omega]

/-- The leaf loop reaches the parent-building phase (`pc = 6420`), advances `x23` by
`1536 * remaining`, and preserves the tree base, commitment pointer and constant call args. -/
theorem commit_leaves_finished (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    finished.pc = 6420 ∧
    finished.getReg .x23 = state.getReg .x23 + BitVec.ofNat 64 (1536 * remaining) ∧
    ∀ reg ∈ [Reg.x9, .x26, .x5, .x11, .x13], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simpa using invariant.pc, by simp, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have regs := commit_block_registers state next reached
    have done := ih next (commit_leaves_next_invariant state next remaining invariant reached) rest
    refine ⟨done.1, ?_, ?_⟩
    · rw [done.2.1, regs.2.2.1, BitVec.add_assoc]
      change state.getReg .x23 + (BitVec.ofNat 64 1536 + BitVec.ofNat 64 (1536 * remaining)) = _
      rw [← BitVec.ofNat_add]
      exact congrArg (fun n => state.getReg .x23 + BitVec.ofNat 64 n) (by omega)
    · intro reg member
      exact (done.2.2 reg member).trans (regs.2.2.2.2 reg (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))

end CommitGolfCandidate
