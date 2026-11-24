import CommitGolfCandidate.SharedPinnedAdaptive

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
local instance SharedPinnedGlobalHitsDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem shared_exceptional_list_hits (sample : ProbComp (Bool × List Row))
    (trace : List Row) (rate : ENNReal)
    (fixed : ∀ row, Pr{let draw ← sample}[draw.1 = false ∧ rowHits draw.2 row = true] ≤ rate) :
    Pr{let draw ← sample}[draw.1 = true ∨ ∃ row ∈ trace, rowHits draw.2 row = true] ≤
      Pr{let draw ← sample}[draw.1 = true] + (trace.length : ENNReal)*rate := by
  have enlarged := prEvent_mono sample
    (p := fun draw => draw.1 = true ∨ ∃ row ∈ trace, rowHits draw.2 row = true)
    (q := fun draw => draw.1 = true ∨ ∃ row ∈ trace,
      draw.1 = false ∧ rowHits draw.2 row = true) (by
        rintro draw (bad | ⟨row, present, hit⟩)
        · exact Or.inl bad
        · cases flag : draw.1 with
          | true => exact Or.inl rfl
          | false => exact Or.inr ⟨row, present, rfl, hit⟩)
  exact enlarged.trans ((prEvent_or_le sample _ _).trans
    (add_le_add le_rfl (prEvent_list_le trace sample
      (fun row draw => draw.1 = false ∧ rowHits draw.2 row = true) rate
      (fun row _ => fixed row))))

theorem shared_exceptional_reference_hits {α : Type}
    (sample : ProbComp (Bool × List Row)) (rate : ENNReal)
    (compress : Compression) (p : BiPermutation Block) (observer : OracleComp World α)
    (budget : Nat) (bounded : QueryBounded observer budget)
    (fixed : ∀ row, Pr{let draw ← sample}[draw.1 = false ∧ rowHits draw.2 row = true] ≤ rate) :
    Pr{let result ← (do
      let draw ← sample
      flaggedRun (fixedOracle compress p) (marksReferencePair p draw.2) observer draw.1)}[
      result.2.2 = true] ≤
      Pr{let draw ← sample}[draw.1 = true] + (budget : ENNReal)*rate := by
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let mark (draw : Bool × List Row) (trace : α × List Row) : α × Unit × Bool :=
    (trace.1, (), draw.1 || trace.2.any (rowHits draw.2))
  have order := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm sample traced (fun draw trace => pure (mark draw trace)))
  have expand (draw : Bool × List Row) :
      flaggedRun oracle (marksReferencePair p draw.2) observer draw.1 =
        traced >>= fun trace => pure (mark draw trace) := by
    unfold oracle traced mark
    rw [flagged_reference_trace]
    simp only [map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [order.prEvent_eq (fun result => result.2.2 = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro trace present
  simp only [bind_pure_comp, prEvent_map, mark, Bool.or_eq_true, List.any_eq_true]
  have limit := trace_permutation_length oracle observer budget bounded trace present
  have count : (trace.2.length : ENNReal) ≤ (budget : ENNReal) := by exact_mod_cast limit
  exact (shared_exceptional_list_hits sample trace.2 rate fixed).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right count zero_le))

end TwoPermutationPrototype.Sampling
