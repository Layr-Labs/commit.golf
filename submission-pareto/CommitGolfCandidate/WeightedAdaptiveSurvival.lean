import CommitGolfCandidate.PredictableSurvival
import CommitGolfCandidate.WeightedAdvance

/-! Finite weighted survival for a model with predictable counter forecasts. -/
namespace CommitGolfCandidate.Chained.Weighted
open CommitGolf OracleComp OracleSpec
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem adaptive_weighted_bound {State α : Type} (model : PredictableSurvival.Model State)
    (rate width : ι → Nat) (counts : State → ι → Nat) (kind : State → PublicSpec.Domain → Option ι)
    (mass_eq : ∀ s, model.mass s = potential width (counts s))
    (hazard_eq : ∀ s query, model.hazard s query = hazard width (counts s) (kind s query))
    (rate_bound : ∀ k, rate k ≤ 8) (dense : ∀ k, 2^238 ≤ (rate k)^2*2^(width k))
    (publicCeiling workCeiling : Nat) (small : 8*workCeiling < 2^238)
    (forecast : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat),
      model.valid s known → ¬ model.bad s → known < publicCeiling →
        work rate (advance (counts s) (kind s query)) ≤ workCeiling)
    (program : OracleComp World α) (budget known : Nat) (bounded : PublicQueryBound program budget)
    (room : known+budget ≤ publicCeiling) (s : State) (valid : model.valid s known) (safe : ¬ model.bad s) :
    Pr{let result ← model.run program s}[model.bad result.2] ≤
      1-ENNReal.ofReal (Real.exp (-(workCeiling : ℝ)^2/(2*(2^238-8*(workCeiling : ℝ)))))/model.mass s := by
  apply model.adaptive_survival _ publicCeiling
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) ?_ program budget known bounded room s valid safe
  intro query current rank consistent clean remaining
  rw [mass_eq current,hazard_eq current query,← potential_advance]
  exact finite_envelope rate width _ workCeiling rate_bound dense
    (forecast query current rank consistent clean remaining) small

end CommitGolfCandidate.Chained.Weighted
