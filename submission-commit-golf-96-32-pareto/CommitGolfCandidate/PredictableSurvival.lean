import CommitGolfCandidate.CompressionROM

/-! Adaptive survival for a reply-independent potential forecast. -/
namespace CommitGolfCandidate.PredictableSurvival
open CommitGolf OracleComp OracleSpec

structure Model (State : Type) where
  handler : QueryImpl World (StateT State ProbComp)
  valid : State → Nat → Prop
  bad : State → Prop
  mass : State → ENNReal
  hazard : State → PublicSpec.Domain → ENNReal
  coins : ∀ (n : unifSpec.Domain) (s : State),
    (handler (.inl n)).run s =
      (do let answer ← (liftM (unifSpec.query n) : ProbComp _); pure (answer,s))
  preserves : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat),
    valid s known → ∀ result ∈ support ((handler (.inr query)).run s), valid result.2 (known+1)
  fresh : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat), valid s known → ¬ bad s →
    Pr{let result ← (handler (.inr query)).run s}[bad result.2] ≤ hazard s query
  mass_step : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat), valid s known → ¬ bad s →
    ∀ result ∈ support ((handler (.inr query)).run s), ¬ bad result.2 →
      mass result.2 = mass s*(1-hazard s query)

namespace Model

def run {State α : Type} (model : Model State) (program : OracleComp World α) (s : State) :
    ProbComp (α × State) := (simulateQ model.handler program).run s

private theorem loss_step {p a y : ENNReal} (pa : p ≤ a) (p1 : p ≤ 1) (y1 : y ≤ 1) :
    p+(1-y)*(1-p) ≤ 1-(1-a)*y := by
  have xfin : (1-p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have expand : (1-y)*(1-p) = 1*(1-p)-y*(1-p) := ENNReal.sub_mul (fun _ _ => xfin)
  rw [expand,one_mul]
  have yx : y*(1-p) ≤ 1-p := mul_le_of_le_one_left' y1
  rw [add_comm p,ENNReal.sub_add_eq_add_sub yx (ne_top_of_le_ne_top xfin yx),
    tsub_add_cancel_of_le p1]
  apply tsub_le_tsub_left
  calc (1-a)*y ≤ (1-p)*y := by gcongr
    _ = y*(1-p) := mul_comm _ _

theorem potential_step {p a L M : ENNReal} (pa : p ≤ a) (p1 : p ≤ 1)
    (positive : 0 < L) (lower : L ≤ M*(1-a)) :
    p+(1-L/(M*(1-a)))*(1-p) ≤ 1-L/M := by
  have nonzero : (1-a) ≠ 0 := by
    intro zero
    have pos := positive.trans_le lower
    rw [zero,mul_zero] at pos
    exact (lt_irrefl _ pos)
  have finite : (1-a) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have ratio : L/(M*(1-a)) ≤ 1 := ENNReal.div_le_of_le_mul (by simpa only [one_mul] using lower)
  have cancel : (1-a)*(L/(M*(1-a))) = L/M := by
    calc
      _ = (L*(1-a))/(M*(1-a)) := by rw [← mul_div_assoc,mul_comm (1-a) L]
      _ = _ := ENNReal.mul_div_mul_right L M nonzero finite
  simpa only [cancel] using loss_step pa p1 ratio

/-- The forecast lower bound is checked before sampling each public reply. -/
theorem adaptive_survival {State α : Type} (model : Model State) (L : ENNReal) (ceiling : Nat)
    (positive : 0 < L)
    (forecast : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat),
      model.valid s known → ¬ model.bad s → known < ceiling → L ≤ model.mass s*(1-model.hazard s query))
    (program : OracleComp World α) (budget known : Nat) (bounded : PublicQueryBound program budget)
    (room : known+budget ≤ ceiling) (s : State) (valid : model.valid s known) (safe : ¬ model.bad s) :
    Pr{let result ← model.run program s}[model.bad result.2] ≤ 1-L/model.mass s := by
  classical
  induction program using OracleComp.inductionOn generalizing budget known s with
  | pure value =>
    rw [show model.run (pure value) s = pure (value,s) by simp [run],prEvent_pure]
    simp only [safe,ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    have unfoldRun : model.run ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (model.handler query).run s >>= fun result => model.run (next result.1) result.2 := by
      simp [run,simulateQ_bind,StateT.run_bind]
    rw [unfoldRun]
    rcases query with coins | publicQuery
    · rw [model.coins]
      simp only [bind_assoc,pure_bind]
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun answer _ =>
        ih answer budget known (by simpa only [Oracle.callCost,Nat.sub_zero] using bounded.2 answer)
          room s valid safe
    · have positiveBudget : 1 ≤ budget := bounded.1
      have continuation : ∀ result ∈ support ((model.handler (.inr publicQuery)).run s),
          ¬ model.bad result.2 →
          Pr{let last ← model.run (next result.1) result.2}[model.bad last.2] ≤
            1-L/(model.mass s*(1-model.hazard s publicQuery)) := by
        intro result reached good
        have recursive := ih result.1 (budget-1) (known+1) (bounded.2 result.1) (by omega) result.2
          (model.preserves publicQuery s known valid result reached) good
        simpa only [model.mass_step publicQuery s known valid safe result reached good] using recursive
      have combined := prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support
        ((model.handler (.inr publicQuery)).run s) (fun result => model.run (next result.1) result.2)
        (fun result => model.bad result.2) (fun result => model.bad result.2) continuation
      rw [prEvent_not_eq_one_sub] at combined
      exact combined.trans (potential_step (model.fresh publicQuery s known valid safe)
        (prEvent_le_one _) positive (forecast publicQuery s known valid safe (by omega)))

end Model
end CommitGolfCandidate.PredictableSurvival
