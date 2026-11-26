import CommitGolfCandidate.TruncBProgress
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
attribute [local irreducible] lowerHash

theorem prefixNext (H : Compression) (input : CheckInput) (n : Nat) (u : Fin 256) :
    prefixNode H input (n+1) u =
    match prefixNode H input n u with
    | some existing => some existing
    | none => if openingIndex input.positions n/65536=u.val then some (lowerHash H input n) else none := by
  unfold prefixNode
  rw [List.range_succ,List.find?_append]
  cases h : (List.range n).find? (fun r => openingIndex input.positions r/65536 == u.val) with
  | none => by_cases same : openingIndex input.positions n/65536=u.val <;> simp [same]
  | some r => simp

theorem prefixEmpty (H : Compression) (input : CheckInput) (u : Fin 256) :
    prefixNode H input 0 u=none := rfl

/-- When the duplicate comparison succeeds, adding one record preserves all
earlier witnesses and authenticates the new record at its own level-8 bucket. -/
theorem extendConsistent (H : Compression) (input : CheckInput) (n : Nat)
    (old : ∀ r<n, ∀ u : Fin 256, openingIndex input.positions r/65536=u.val →
      prefixNode H input n u=some (lowerHash H input r))
    (confirmed : ∀ u : Fin 256, openingIndex input.positions n/65536=u.val →
      ∀ d, prefixNode H input n u=some d → d=lowerHash H input n) :
    ∀ r<n+1, ∀ u : Fin 256, openingIndex input.positions r/65536=u.val →
      prefixNode H input (n+1) u=some (lowerHash H input r) := by
  intro r hr u index
  rw [prefixNext]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr with prev|eqn
  · rw [old r prev u index]
  · subst r
    cases e : prefixNode H input n u with
    | none => simp [index]
    | some d => simp [confirmed u index d e]

end CommitGolfCandidate.Trunc.Batch
