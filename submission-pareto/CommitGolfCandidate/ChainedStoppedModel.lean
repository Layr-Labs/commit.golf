import CommitGolfCandidate.ChainedStoppedHazard
import CommitGolfCandidate.WeightedAdaptiveSurvival

/-! The concrete source-backed stopped process instantiates predictable survival. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec

noncomputable def model (limit : Nat) (enc : Encoding) (calls width : Height → Nat)
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256) : PredictableSurvival.Model State where
  handler := handler limit enc calls width
  valid s known := Core limit enc calls width s ∧ s.oracle.base.count ≤ known
  bad := State.won
  mass s := Weighted.potential (Counters.widths width) s.counts
  hazard s query := Weighted.hazard (Counters.widths width) s.counts (kind limit enc calls s query)
  coins := by intro coins s; rfl
  preserves := by
    intro query s known consistent result reached
    change result ∈ support (do
      let answer ← (Observer.handler (.inr query)).run s.oracle
      pure (answer.1,finish limit enc calls width s query answer.2)) at reached
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
    obtain ⟨answer,sampled,rfl⟩ := reached
    refine ⟨preserves_core small s consistent.1 query answer sampled,?_⟩
    change answer.2.base.count ≤ known+1
    rw [Observer.handler_count query s.oracle answer sampled]
    omega
  fresh := by
    intro query s known consistent safe
    exact fresh_hazard small widthBound s consistent.1 safe query
  mass_step := by
    intro query s known consistent safe result reached lastSafe
    change result ∈ support (do
      let answer ← (Observer.handler (.inr query)).run s.oracle
      pure (answer.1,finish limit enc calls width s query answer.2)) at reached
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at reached
    obtain ⟨answer,sampled,rfl⟩ := reached
    exact Weighted.potential_advance (Counters.widths width) s.counts (kind limit enc calls s query)

theorem adaptive_bound {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (rateBound : ∀ k, Counters.rate calls k ≤ 8)
    (dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k))
    (finite : 8*(limit+1) < 2^238) {α : Type} (program : OracleComp World α)
    (budget known : Nat) (bounded : PublicQueryBound program budget) (room : known+budget ≤ limit)
    (s : State) (core : Core limit enc calls width s) (counted : s.oracle.base.count ≤ known)
    (safe : ¬ s.won) :
    Pr{let result ← (model limit enc calls width small widthBound).run program s}[result.2.won] ≤
      1-ENNReal.ofReal (Real.exp (-((limit+1 : Nat) : ℝ)^2/(2*(2^238-8*((limit+1 : Nat) : ℝ)))))/
        Weighted.potential (Counters.widths width) s.counts := by
  apply Weighted.adaptive_weighted_bound (model limit enc calls width small widthBound)
    (Counters.rate calls) (Counters.widths width) State.counts (kind limit enc calls)
    (fun _ => rfl) (fun _ _ => rfl) rateBound dense limit (limit+1) finite
    ?_ program budget known bounded room s ⟨core,counted⟩ safe
  intro query current rank consistent clean remaining
  exact forecast current rank consistent.1 consistent.2 remaining small query

end CommitGolfCandidate.Chained.Stopped
