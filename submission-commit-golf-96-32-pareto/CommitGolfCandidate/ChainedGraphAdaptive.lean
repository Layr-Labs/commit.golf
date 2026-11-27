import CommitGolfCandidate.ChainedGraphHazard
import CommitGolfCandidate.CompressionROM

/-! Adaptive accumulation of the full-width query-graph exceptions. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec
open scoped BigOperators

structure GraphBudget (State : Type) where
  handler : QueryImpl World (StateT State ProbComp)
  valid : State → Nat → Prop
  bad : State → Prop
  coins : ∀ (n : unifSpec.Domain) (s : State),
    (handler (.inl n)).run s =
      (do let answer ← (liftM (unifSpec.query n) : ProbComp _); pure (answer,s))
  preserves : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat), valid s known →
    ∀ result ∈ support ((handler (.inr query)).run s), valid result.2 (known+1)
  fresh : ∀ (query : PublicSpec.Domain) (s : State) (known : Nat), valid s known → ¬bad s →
    Pr{let result ← (handler (.inr query)).run s}[bad result.2] ≤
      ((2*known : Nat) : ENNReal)/2^256

namespace GraphBudget

noncomputable def charge (known budget : Nat) : ENNReal :=
  ∑ i ∈ Finset.range budget, ((2*(known+i) : Nat) : ENNReal)/2^256

theorem charge_zero (known : Nat) : charge known 0 = 0 := by simp [charge]

theorem charge_succ (known budget : Nat) :
    charge known (budget+1) = ((2*known : Nat) : ENNReal)/2^256+charge (known+1) budget := by
  unfold charge
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 3
  omega

def run {State α : Type} (model : GraphBudget State) (program : OracleComp World α)
    (state : State) : ProbComp (α × State) := (simulateQ model.handler program).run state

theorem adaptive_bound {State α : Type} (model : GraphBudget State)
    (program : OracleComp World α) (budget known : Nat) (bounded : PublicQueryBound program budget)
    (state : State) (valid : model.valid state known) (safe : ¬model.bad state) :
    Pr{let result ← model.run program state}[model.bad result.2] ≤ charge known budget := by
  classical
  induction program using OracleComp.inductionOn generalizing budget known state with
  | pure value =>
    rw [show model.run (pure value) state = pure (value,state) by simp [run],prEvent_pure]
    simp only [safe,ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    have unfoldRun : model.run ((liftM (World.query query) : OracleComp World _) >>= next) state =
        (model.handler query).run state >>= fun result => model.run (next result.1) result.2 := by
      simp [run,simulateQ_bind,StateT.run_bind]
    rw [unfoldRun]
    rcases query with coins | publicQuery
    · rw [model.coins]
      simp only [bind_assoc,pure_bind]
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun answer _ =>
        ih answer budget known (by simpa only [Oracle.callCost,Nat.sub_zero] using bounded.2 answer)
          state valid safe
    · have positive : 1 ≤ budget := bounded.1
      have continuation : ∀ result ∈ support ((model.handler (.inr publicQuery)).run state),
          ¬model.bad result.2 →
          Pr{let last ← model.run (next result.1) result.2}[model.bad last.2] ≤ charge (known+1) (budget-1) := by
        intro result reached good
        exact ih result.1 (budget-1) (known+1) (bounded.2 result.1) result.2
          (model.preserves publicQuery state known valid result reached) good
      have combined := prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support
        ((model.handler (.inr publicQuery)).run state)
        (fun result => model.run (next result.1) result.2)
        (fun result => model.bad result.2) (fun result => model.bad result.2) continuation
      rw [prEvent_not_eq_one_sub] at combined
      refine combined.trans ?_
      have smaller : charge (known+1) (budget-1)*
          (1-Pr{let result ← (model.handler (.inr publicQuery)).run state}[model.bad result.2]) ≤
          charge (known+1) (budget-1) := mul_le_of_le_one_right' tsub_le_self
      calc
        _ ≤ Pr{let result ← (model.handler (.inr publicQuery)).run state}[model.bad result.2]+
            charge (known+1) (budget-1) := add_le_add le_rfl smaller
        _ ≤ ((2*known : Nat) : ENNReal)/2^256+charge (known+1) (budget-1) :=
          add_le_add (model.fresh publicQuery state known valid safe) le_rfl
        _ = charge known budget := by
          rw [show budget = (budget-1)+1 by omega,charge_succ]
          simp

theorem charge_empty (budget : Nat) : charge 0 budget =
    ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  have summed : (∑ i ∈ Finset.range budget, 2*i) = budget*(budget-1) := by
    rw [← Finset.mul_sum,Nat.mul_comm 2,Finset.sum_range_id_mul_two]
  unfold charge
  simp only [Nat.zero_add]
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [← Finset.mul_sum,← Nat.cast_sum,summed]

theorem from_empty {State α : Type} (model : GraphBudget State)
    (program : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound program budget)
    (state : State) (valid : model.valid state 0) (safe : ¬model.bad state) :
    Pr{let result ← model.run program state}[model.bad result.2] ≤
      ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  simpa only [charge_empty] using adaptive_bound model program budget 0 bounded state valid safe

end GraphBudget
end CommitGolfCandidate.Chained
