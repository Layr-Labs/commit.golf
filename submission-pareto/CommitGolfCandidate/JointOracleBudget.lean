import CommitGolfCandidate.Leaf243CombinedMargin

/-! Adaptive survival under a single public-query budget. The model supplies a
conditional bad-answer bound for the oracle actually queried at each step. -/

namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

structure JointOracleBudget (State : Type) where
  handler : QueryImpl World (StateT State ProbComp)
  valid : State → Nat → Prop
  bad : State → Prop
  coins : ∀ (n : unifSpec.Domain) (s : State),
    (handler (.inl n)).run s =
      (do let answer ← (liftM (unifSpec.query n) : ProbComp _); pure (answer, s))
  preserves : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat),
    valid s known → ∀ result ∈ support ((handler (.inr query)).run s),
      valid result.2 (known + 1)
  fresh : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat),
    valid s known → ¬ bad s →
      Pr{let result ← (handler (.inr query)).run s}[bad result.2] ≤
        ((known + 1 : Nat) : ENNReal) / 2^238

namespace JointOracleBudget

def run {State α : Type} (model : JointOracleBudget State)
    (program : OracleComp World α) (s : State) : ProbComp (α × State) :=
  (simulateQ model.handler program).run s

private theorem step {p a y : ENNReal} (pa : p ≤ a) (p1 : p ≤ 1) (y1 : y ≤ 1) :
    p + (1-y)*(1-p) ≤ 1-(1-a)*y := by
  have xfin : (1-p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have expand : (1-y)*(1-p) = 1*(1-p)-y*(1-p) :=
    ENNReal.sub_mul (fun _ _ => xfin)
  rw [expand, one_mul]
  have yx : y*(1-p) ≤ 1-p := mul_le_of_le_one_left' y1
  rw [add_comm p, ENNReal.sub_add_eq_add_sub yx (ne_top_of_le_ne_top xfin yx),
    tsub_add_cancel_of_le p1]
  apply tsub_le_tsub_left
  calc (1-a)*y ≤ (1-p)*y := by gcongr
    _ = y*(1-p) := mul_comm _ _

/-- Private coins preserve the rank; each public query consumes exactly one factor. -/
theorem adaptive_survival {State α : Type} (model : JointOracleBudget State)
    (program : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound program budget) (s : State)
    (valid : model.valid s known) (safe : ¬ model.bad s) :
    Pr{let result ← model.run program s}[model.bad result.2] ≤
      1-survival 238 (known+1) budget := by
  classical
  induction program using OracleComp.inductionOn generalizing budget known s with
  | pure value =>
    rw [show model.run (pure value) s = pure (value,s) by simp [run], prEvent_pure]
    simp only [safe, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    have unfoldRun : model.run ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (model.handler query).run s >>= fun result => model.run (next result.1) result.2 := by
      simp [run, simulateQ_bind, StateT.run_bind]
    rw [unfoldRun]
    rcases query with coins | publicQuery
    · rw [model.coins]
      simp only [bind_assoc, pure_bind]
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun answer _ =>
        ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
          s valid safe
    · have positive : 1 ≤ budget := bounded.1
      have continuation : ∀ result ∈ support ((model.handler (.inr publicQuery)).run s),
          ¬ model.bad result.2 →
          Pr{let last ← model.run (next result.1) result.2}[model.bad last.2] ≤
            1-survival 238 (known+1+1) (budget-1) := by
        intro result reached good
        exact ih result.1 (budget-1) (known+1) (bounded.2 result.1) result.2
          (model.preserves publicQuery s known valid result reached) good
      have combined := prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support
        ((model.handler (.inr publicQuery)).run s)
        (fun result => model.run (next result.1) result.2)
        (fun result => model.bad result.2) (fun result => model.bad result.2) continuation
      rw [prEvent_not_eq_one_sub] at combined
      refine combined.trans ?_
      rw [show budget = (budget-1)+1 from by omega, survival_succ, Nat.add_sub_cancel]
      exact step (model.fresh publicQuery s known valid safe) (prEvent_le_one _)
        (survival_le_one 238 _ _)

end JointOracleBudget
end CommitGolfCandidate
