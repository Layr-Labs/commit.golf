import CommitGolfCandidate.CommitParents

/-! Residual-count proof for the actual pointer-terminated parent loop. The
natural index is ghost state only: x20 stays unchanged in the machine. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let answer ← World.query (.inr (commitParentQuery state))
      commitParents (commitParentNextState (commitParentState state answer)) remaining

/-- Access validity and alignment for every remaining pair of children and parent. -/
def ParentBuffers (base : Word) (remaining : Nat) : Prop :=
  ∀ node, 0 < node → node ≤ remaining →
    rangeValid (base + (BitVec.ofNat 64 node <<< 6)) 64 = true ∧
    rangeValid (base + (BitVec.ofNat 64 node <<< 5)) 32 = true ∧
    (base + (BitVec.ofNat 64 node <<< 6)).toNat % 8 = 0 ∧
    (base + (BitVec.ofNat 64 node <<< 5)).toNat % 8 = 0

/-- The two machine pointers name the natural residual node index. -/
def ParentPointerInvariant (state : MachineState) (remaining : Nat) : Prop :=
  state.getReg .x10 = state.getReg .x9 + BitVec.ofNat 64 (64 * remaining) ∧
  state.getReg .x12 = state.getReg .x9 + BitVec.ofNat 64 (32 * remaining)

theorem commit_parent_step_pointers (state : MachineState) (answer : BitVec 256)
    (remaining : Nat) (pointers : ParentPointerInvariant state (remaining+1)) :
    ParentPointerInvariant (commitParentNextState (commitParentState state answer)) remaining := by
  unfold ParentPointerInvariant at pointers ⊢
  rw [commit_parent_step_input, commit_parent_step_output,
    commit_parent_step_register state answer .x9 (by simp), pointers.1, pointers.2]
  exact ⟨parent_pointer_decrement _ 64 remaining, parent_pointer_decrement _ 32 remaining⟩

theorem commit_parent_step_pc_index (state : MachineState) (answer : BitVec 256)
    (remaining : Nat) (bounded : remaining < 2^24)
    (pointers : ParentPointerInvariant state (remaining+1)) :
    (commitParentNextState (commitParentState state answer)).pc =
      if remaining = 0 then 4404 else 4388 := by
  rw [commit_parent_step_pc, pointers.2]
  change (if state.getReg .x9 + BitVec.ofNat 64 (32*(remaining+1)) -
      BitVec.ofNat 64 32 = state.getReg .x9 then _ else _) = _
  rw [parent_pointer_decrement]
  simp only [parent_pointer_done_iff _ remaining bounded]

attribute [local irreducible] execute pointerParentState pointerParentNextState

/-- The final false pointer branch reaches the terminal jump. Required tree
and output registers remain unchanged under arbitrary compression replies. -/
theorem commit_parents_finished (state : MachineState) (remaining : Nat)
    (bounded : remaining < 2 ^ 24) (pointers : ParentPointerInvariant state remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    (0 < remaining → finished.pc = 4404) ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by omega, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have done := ih _ (by omega) (commit_parent_step_pointers state answer remaining pointers) reached
    refine ⟨?_, ?_⟩
    · intro _
      by_cases empty : remaining = 0
      · subst remaining
        simp only [commitParents, support_pure, Set.mem_singleton_iff] at reached
        subst finished
        rw [commit_parent_step_pc_index state answer 0 (by decide) pointers]
        rfl
      · exact done.1 (Nat.pos_of_ne_zero empty)
    · intro reg member
      apply (done.2 reg member).trans
      apply commit_parent_step_register
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      tauto

end CommitGolfCandidate
