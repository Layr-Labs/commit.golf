import CommitGolfCandidate.JointOracle241Recorded
import CommitGolfCandidate.ReconstructedBindingMargin

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.JointOracle241

private theorem mix {p a y : ENNReal} (pa : p ≤ a) (p1 : p ≤ 1) (y1 : y ≤ 1) :
    p + (1-y)*(1-p) ≤ 1-(1-a)*y := by
  have finite : (1-p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have expan : (1-y)*(1-p) = 1*(1-p)-y*(1-p) := ENNReal.sub_mul (fun _ _ => finite)
  rw [expan,one_mul]
  have h : y*(1-p) ≤ 1-p := mul_le_of_le_one_left' y1
  rw [add_comm p, ENNReal.sub_add_eq_add_sub h (ne_top_of_le_ne_top finite h),tsub_add_cancel_of_le p1]
  apply tsub_le_tsub_left
  calc (1-a)*y ≤ (1-p)*y := by gcongr
       _ = y*(1-p) := mul_comm _ _

private theorem exp_le_one' {v : ℝ} (hv : v ≤ 0) : ENNReal.ofReal (Real.exp v) ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr hv)

/-- Exponential survival with charges released only when a paid chain finishes.
The charge of a query is predictable before its answer. A live reply pays the
charge; every other reply is covered by the stated one-step probability. -/
theorem adaptive_exponential (good : State → Prop) (credit : State → ℝ) (cap : ℝ) (maxQueries : Nat)
      (step : ∀ (query : PublicSpec.Domain) (s : State), s.count < maxQueries → good s →
      ∃ (reject : PublicSpec.Range query × State → Prop) (delta : ℝ),
        0 ≤ delta ∧ credit s + delta ≤ cap ∧
        Pr{let r ← handler (.inr query) s}[reject r] ≤ 1-ENNReal.ofReal (Real.exp (-delta)) ∧
        ∀ r ∈ support (handler (.inr query) s), ¬ reject r → good r.2 ∧ credit s + delta ≤ credit r.2)
    {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) (s : State)
    (room : s.count + budget ≤ maxQueries) (start : good s) :
    Pr{let r ← model.run program s}[¬ good r.2] ≤ 1-ENNReal.ofReal (Real.exp (credit s-cap)) := by
  classical
  induction program using OracleComp.inductionOn generalizing s budget with
  | pure value =>
    have rp : model.run (pure value) s = pure (value,s) := by simp [JointOracleBudget.run]
    rw [rp,prEvent_pure]
    simp [start]
  | query_bind query next ih =>
    rw [run_query]
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    rcases query with coin | pub
    · simp only [handler, bind_assoc, pure_bind]
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun x _ =>
        ih x budget (by simpa [Oracle.callCost] using bounded.2 x) s room start
    · have positive : 1 ≤ budget := bounded.1
      obtain ⟨bad,δ,hδ,cap',chance,live⟩ := step pub s (by omega) start
      let surv := ENNReal.ofReal (Real.exp (credit s + δ - cap))
      have after : ∀ r ∈ support (handler (.inr pub) s), ¬ bad r →
          Pr{let last ← model.run (next r.1) r.2}[¬ good last.2] ≤ 1-surv := by
        intro r hr ok
        have count := handler_count pub s r hr
        obtain ⟨gs,up⟩ := live r hr ok
        refine (ih r.1 (budget-1) (bounded.2 _) r.2 (by omega) gs).trans ?_
        apply tsub_le_tsub_left
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
      have comb := prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support
        (handler (.inr pub) s) (fun r => model.run (next r.1) r.2)
        bad (fun r => ¬ good r.2) after
      nth_rw 2 [prEvent_not_eq_one_sub] at comb
      have endLe : surv ≤ 1 := exp_le_one' (by linarith)
      have lossLe : ENNReal.ofReal (Real.exp (-δ)) ≤ 1 := exp_le_one' (by linarith)
      refine comb.trans ((mix chance (prEvent_le_one _) endLe).trans ?_)
      rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top lossLe]
      unfold surv
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      ring_nf
      exact le_rfl

end CommitGolfCandidate.Reconstruction.Binding
