import CommitGolfCandidate.QueryBudget
import CommitGolf.Hiding

/-! Transfer the contract's two-stage hiding budget to the structural public-query
bounds used by the lazy-oracle proofs. Private coin requests remain free. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

private theorem some_supported_result {α : Type} (computation : OracleComp World α) :
    ∃ result, result ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp⟩
  | query_bind query next ih =>
    obtain ⟨result, reached⟩ := ih default
    exact ⟨result, (mem_support_bind_iff _ _ _).mpr
      ⟨default, mem_support_query query default, reached⟩⟩

private theorem counted_query_support {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (answer : World.Range query)
    (result : α × Nat) (reached : result ∈ support (Hiding.counted (next answer))) :
    (result.1, Oracle.callCost query+result.2) ∈ support
      (Hiding.counted ((liftM (World.query query) : OracleComp World _) >>= next)) := by
  rw [Hiding.counted, costDist, instrumentedRun, simulateQ_bind, simulateQ_query, WriterT.run_bind]
  refine (mem_support_bind_iff _ _ _).mpr
    ⟨(answer, (Multiplicative.ofAdd (Oracle.callCost query) : Multiplicative Nat)), ?_, ?_⟩
  · simp [QueryImpl.withAddCost, QueryImpl.withCost]
  · change (result.1, Oracle.callCost query+result.2) ∈ support
      ((fun value : α × Nat => (value.1, Oracle.callCost query+value.2)) <$>
        Hiding.counted (next answer))
    rw [support_map]
    exact ⟨result, reached, by simp [Nat.add_comm]⟩

/-- A bound on every instrumented execution entails the recursive public-query
bound, including continuations at every possible oracle reply. -/
theorem public_query_bound_of_counted_support {α : Type} (computation : OracleComp World α)
    (budget : Nat) (bounded : ∀ result ∈ support (Hiding.counted computation), result.2 ≤ budget) :
    PublicQueryBound computation budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query))
    constructor
    · obtain ⟨result, reached⟩ := some_supported_result (Hiding.counted (next default))
      have bound := bounded _ (counted_query_support query next default result reached)
      change Oracle.callCost query+result.2 ≤ budget at bound
      omega
    · intro answer
      apply ih answer
      intro result reached
      have bound := bounded _ (counted_query_support query next answer result reached)
      change Oracle.callCost query+result.2 ≤ budget at bound
      omega

theorem hiding_choose_query_bound {AdversaryState Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    PublicQueryBound adversary.choose budget :=
  public_query_bound_of_counted_support _ _ (fun result reached => (bounded result reached).1)

/-- The observing stage receives only the budget left by its particular first
stage execution, for every possible root and proof it might be shown. -/
theorem hiding_observe_query_bound {AdversaryState Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (first : Hiding.HidingChallenge AdversaryState openingSize × Nat)
    (reached : first ∈ support (Hiding.counted adversary.choose))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe first.1.aux root proof) (budget-first.2) := by
  apply public_query_bound_of_counted_support
  intro last observed
  have bound := (bounded first reached).2 root proof last observed
  omega

end CommitGolfCandidate
