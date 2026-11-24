import CommitGolfCandidate.ChainedLevelLoop

/-! Whole-level cursor displacements and memory preservation outside destination spans. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem level_trace_source (remaining : Nat) (s out : MachineState) (h : Height)
    (reached : out ∈ support (levelTrace h remaining s)) :
    out.getReg .x6 = cursorAt (s.getReg .x6) 64 remaining := by
  induction remaining generalizing s with
  | zero =>
    simp only [levelTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact (cursor_at_zero _ _).symm
  | succ remaining ih =>
    simp only [levelTrace,mem_support_bind_iff] at reached
    obtain ⟨next,first,last⟩ := reached
    rw [ih next last,node_source s next h first]
    exact cursor_at_next (s.getReg .x6) 64 remaining

theorem level_trace_target (remaining : Nat) (s out : MachineState) (h : Height)
    (reached : out ∈ support (levelTrace h remaining s)) :
    out.getReg .x7 = cursorAt (s.getReg .x7) 32 remaining := by
  induction remaining generalizing s with
  | zero =>
    simp only [levelTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    exact (cursor_at_zero _ _).symm
  | succ remaining ih =>
    simp only [levelTrace,mem_support_bind_iff] at reached
    obtain ⟨next,first,last⟩ := reached
    rw [ih next last,node_target s next h first]
    exact cursor_at_next (s.getReg .x7) 32 remaining

theorem level_trace_memory (remaining : Nat) (s out : MachineState) (h : Height)
    (args : LoopArgs s 256) (reached : out ∈ support (levelTrace h remaining s))
    (query : Word) (outside : OutsideScratch query)
    (avoid : ∀ i, i < remaining → ∀ j : Fin 4,
      query ≠ cursorAt (s.getReg .x7) 32 i+BitVec.ofNat 64 (8*j.val)) :
    out.getMem query = s.getMem query := by
  induction remaining generalizing s with
  | zero =>
    simp only [levelTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [levelTrace,mem_support_bind_iff] at reached
    obtain ⟨next,first,last⟩ := reached
    have rest : ∀ i, i < remaining → ∀ j : Fin 4,
        query ≠ cursorAt (next.getReg .x7) 32 i+BitVec.ofNat 64 (8*j.val) := by
      intro i inside j
      rw [node_target s next h first]
      have shift := cursor_at_next (s.getReg .x7) 32 i
      rw [show BitVec.ofNat 64 32 = (32 : Word) from rfl] at shift
      rw [shift]
      exact avoid (i+1) (by omega) j
    rw [ih next (args.node h first) last rest]
    apply node_memory_outside s next h args first query outside
    intro j
    simpa only [cursor_at_zero] using avoid 0 (by omega) j

end CommitGolfCandidate.Chained.Native
