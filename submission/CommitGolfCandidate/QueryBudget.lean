import CommitGolfCandidate.CountingCoins
import VCVio.OracleComp.QueryTracking.QueryBound

/-! Public-query budget enforcement used only in the security reduction.
Private coins remain unrestricted. This does not change the submitted programs
or replace the challenge's event-based budget with an assumption on the adversary. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- A structural bound counting both public primitives and no private coins. -/
def PublicQueryBound {α : Type} (computation : OracleComp World α) (budget : Nat) : Prop :=
  IsQueryBound computation budget (fun query left => Oracle.callCost query ≤ left)
    (fun query left => left - Oracle.callCost query)

theorem PublicQueryBound.mono {α : Type} {computation : OracleComp World α} {budget larger : Nat}
    (bounded : PublicQueryBound computation budget) (increase : budget ≤ larger) :
    PublicQueryBound computation larger := by
  induction computation using OracleComp.inductionOn generalizing budget larger with
  | pure value => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    exact ⟨bounded.1.trans increase, fun answer =>
      ih answer (bounded.2 answer) (Nat.sub_le_sub_right increase _)⟩

/-- A bound counting every query also bounds the public subset. -/
theorem public_query_bound_of_total {α : Type} {computation : OracleComp World α} {budget : Nat}
    (bounded : IsTotalQueryBound computation budget) : PublicQueryBound computation budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    have cost : Oracle.callCost query ≤ 1 := by cases query <;> simp [Oracle.callCost]
    refine ⟨cost.trans bounded.1, fun answer => ?_⟩
    exact (ih answer (bounded.2 answer)).mono (Nat.sub_le_sub_left cost budget)

/-- Sequential composition adds the public budgets while leaving coins free. -/
theorem public_query_bound_bind {α β : Type} {computation : OracleComp World α}
    {next : α → OracleComp World β} {first second : Nat}
    (firstBound : PublicQueryBound computation first) (secondBound : ∀ value, PublicQueryBound (next value) second) :
    PublicQueryBound (computation >>= next) (first + second) := by
  apply isQueryBound_bind (combine := fun left right => left + right) ?_ ?_ firstBound secondBound
  · intro query left right budget allowed
    constructor <;> omega
  · intro query left right budget allowed
    constructor <;> omega

/-- Stop immediately before a public query would exceed the supplied budget.
The original result is returned only when the entire computation fits. -/
def limitPublicQueries {α : Type} (computation : OracleComp World α) : Nat → OracleComp World (Option α) :=
  OracleComp.recOn computation
    (fun value _ => pure (some value))
    (fun query _ next budget =>
      if Oracle.callCost query ≤ budget then do
        let answer ← (liftM (World.query query) : OracleComp World (World.Range query))
        next answer (budget - Oracle.callCost query)
      else pure none)

theorem limit_public_pure {α : Type} (value : α) (budget : Nat) :
    limitPublicQueries (pure value : OracleComp World α) budget = pure (some value) := rfl

theorem limit_public_query_bind {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (budget : Nat) :
    limitPublicQueries ((liftM (World.query query) : OracleComp World _) >>= next) budget =
      if Oracle.callCost query ≤ budget then
        (liftM (World.query query) : OracleComp World _) >>= fun answer =>
          limitPublicQueries (next answer) (budget - Oracle.callCost query)
      else pure none := rfl

theorem limit_public_bound {α : Type} (computation : OracleComp World α) (budget : Nat) :
    PublicQueryBound (limitPublicQueries computation budget) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    rw [limit_public_query_bind]
    split
    · rename_i allowed
      exact ⟨allowed, fun answer => ih answer _⟩
    · trivial

/-- Exceeding the budget only removes outcomes: the probability of any successful
result after enforcement is exactly its original probability with `calls ≤ budget`.
This is the link needed to use structural ROM bounds for arbitrary adversaries. -/
theorem limit_public_probability {α : Type} (oracle : Oracle) (computation : OracleComp World α)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => ∃ value, result.1 = some value ∧ event value |
      oracle.run (limitPublicQueries computation budget)] =
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | oracle.run computation] := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
    rw [limit_public_pure, oracle_run_pure, oracle_run_pure]
    erw [probEvent_pure, probEvent_pure]
    simp
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · rw [limit_public_query_bind]
      simp only [Oracle.callCost, Nat.zero_le, if_true, Nat.sub_zero]
      change Pr[_ | oracle.run ((liftM (liftM (unifSpec.query coins) : ProbComp _) : OracleComp World _) >>= _)] =
        Pr[_ | oracle.run ((liftM (liftM (unifSpec.query coins) : ProbComp _) : OracleComp World _) >>= _)]
      rw [oracle_run_coins_bind, oracle_run_coins_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro answer
      rw [ih]
    · rw [limit_public_query_bind]
      simp only [Oracle.callCost]
      by_cases allowed : 1 ≤ budget
      · erw [if_pos allowed, oracle_run_public_bind, oracle_run_public_bind]
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        have shifted : (fun result : α × Nat => event result.1 ∧ 1 + result.2 ≤ budget) =
            (fun result => event result.1 ∧ result.2 ≤ budget - 1) := by
          funext result
          apply propext
          constructor <;> rintro ⟨holds, count⟩ <;> exact ⟨holds, by omega⟩
        rw [shifted]
        exact ih _ _
      · erw [if_neg allowed, oracle_run_pure, oracle_run_public_bind]
        erw [probEvent_pure]
        simp only [reduceCtorEq, false_and, exists_false, ite_false,
          bind_pure_comp, probEvent_map, Function.comp_def]
        symm
        apply probEvent_eq_zero
        intro result _ winning
        omega

end CommitGolfCandidate
