import CommitGolfCandidate.ChainedWeightedExponent

/-! Predictable counter updates multiply the weighted survival potential. -/
namespace CommitGolfCandidate.Chained.Weighted
open scoped BigOperators
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def advance (counts : ι → Nat) (kind : Option ι) : ι → Nat :=
  match kind with
  | none => counts
  | some k => Function.update counts k (counts k+1)

noncomputable def hazard (width counts : ι → Nat) (kind : Option ι) : ENNReal :=
  match kind with
  | none => 0
  | some k => (counts k : ENNReal)/2^(width k)

theorem potential_advance (width counts : ι → Nat) (kind : Option ι) :
    potential width (advance counts kind) = potential width counts*(1-hazard width counts kind) := by
  cases kind with
  | none => simp [advance,hazard]
  | some k =>
    have factor : ∀ j, survival (width j) 0 (advance counts (some k) j) =
        survival (width j) 0 (counts j)*(if j=k then 1-(counts k : ENNReal)/2^(width k) else 1) := by
      intro j
      by_cases same : j=k
      · subst j
        simp only [advance,Function.update_self,ite_true]
        unfold survival
        rw [Finset.prod_range_succ]
        simp
      · simp [advance,Function.update_of_ne same,same]
    unfold potential
    simp_rw [factor]
    rw [Finset.prod_mul_distrib]
    simp [hazard]

end CommitGolfCandidate.Chained.Weighted
