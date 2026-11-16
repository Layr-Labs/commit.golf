import CommitGolf.Statements
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Sum
import Mathlib.MeasureTheory.Measure.Prod

/-! Distribution identities for discrete observations used in the candidate proofs. -/
namespace CommitGolfCandidate
open OracleComp MeasureTheory

local instance probabilityDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem distribution_bind_comm {α β γ : Type} [Countable α]
    (left : ProbComp α) (right : ProbComp β) (next : α → β → ProbComp γ) :
    𝒟[do let a ← left; let b ← right; next a b] =
      𝒟[do let b ← right; let a ← left; next a b] := by
  simp_rw [evalDist_bind_of_discrete]
  exact Measure.bind_comm (measurable_from_prod_countable_right
    (fun _ => Measurable.of_discrete))

end CommitGolfCandidate
