import CommitGolfCandidate.ChainedStoppedInitial
import CommitGolfCandidate.ChainedObserverGraph

/-! Forgetting stopped bookkeeping leaves exactly the source-backed observer. -/
namespace CommitGolfCandidate.Chained.Stopped
open CommitGolf OracleComp OracleSpec

theorem handler_project (limit : Nat) (enc : Encoding) (calls width : Height → Nat)
    (query : World.Domain) (s : State) :
    (do let result ← (handler limit enc calls width query).run s; pure (result.1,result.2.oracle)) =
      (Observer.handler query).run s.oracle := by
  rcases query with coins | query
  · rw [Observer.handler_coins]
    rfl
  · change (do
      let result ← (do
        let answer ← (Observer.handler (.inr query)).run s.oracle
        pure (answer.1,finish limit enc calls width s query answer.2))
      pure (result.1,result.2.oracle)) = _
    simp only [bind_assoc,pure_bind,finish,Prod.mk.eta,bind_pure]

theorem run_project {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    {α : Type} (program : OracleComp World α) (s : State) :
    (do let result ← (model limit enc calls width small widthBound).run program s
        pure (result.1,result.2.oracle)) = Observer.run program s.oracle := by
  induction program using OracleComp.inductionOn generalizing s with
  | pure value => simp [PredictableSurvival.Model.run,Observer.run]
  | query_bind query next ih =>
    have rawStep : (model limit enc calls width small widthBound).run
        ((liftM (World.query query) : OracleComp World _) >>= next) s =
        (handler limit enc calls width query).run s >>= fun result =>
          (model limit enc calls width small widthBound).run (next result.1) result.2 := by
      simp [PredictableSurvival.Model.run,model,simulateQ_bind,StateT.run_bind]
    have observerStep : Observer.run ((liftM (World.query query) : OracleComp World _) >>= next) s.oracle =
        (Observer.handler query).run s.oracle >>= fun result => Observer.run (next result.1) result.2 := by
      simp [Observer.run,simulateQ_bind,StateT.run_bind]
    rw [rawStep,observerStep,← handler_project limit enc calls width query s]
    simp only [bind_assoc,pure_bind]
    congr 1
    funext result
    exact ih result.1 result.2

theorem graph_bound {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    {α : Type} (program : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound program budget) :
    Pr{let result ← (model limit enc calls width small widthBound).run program empty}[
      ¬ Good enc result.2.oracle.graph] ≤ ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  have same := congrArg (fun computation : ProbComp (α × Observer.State) =>
    Pr{let result ← computation}[¬ Good enc result.2.graph])
      (run_project (enc := enc) (calls := calls) small widthBound program empty)
  simp only [bind_pure_comp,Functor.map_map] at same
  rw [same]
  exact Observer.graph_from_empty enc program budget bounded

theorem joint_bound {limit : Nat} {enc : Encoding} {calls width : Height → Nat}
    (small : 2*limit < 2^256) (widthBound : ∀ h, width h ≤ 256)
    (rateBound : ∀ k, Counters.rate calls k ≤ 8)
    (dense : ∀ k, 2^238 ≤ (Counters.rate calls k)^2*2^(Counters.widths width k))
    (finite : 8*(limit+1) < 2^238) {α : Type} (program : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound program budget) (room : budget ≤ limit) :
    Pr{let result ← (model limit enc calls width small widthBound).run program empty}[
      result.2.won ∨ ¬ Good enc result.2.oracle.graph] ≤
      (1-ENNReal.ofReal (Real.exp (-((limit+1 : Nat) : ℝ)^2/(2*(2^238-8*((limit+1 : Nat) : ℝ))))))+
        ((budget*(budget-1) : Nat) : ENNReal)/2^256 := by
  exact (prEvent_or_le _ _ _).trans (add_le_add
    (from_empty small widthBound rateBound dense finite program budget bounded room)
    (graph_bound (enc := enc) (calls := calls) small widthBound program budget bounded))

end CommitGolfCandidate.Chained.Stopped
