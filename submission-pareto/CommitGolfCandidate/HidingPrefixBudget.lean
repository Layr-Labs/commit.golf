import CommitGolfCandidate.TwoPermutationPosterior
import CommitGolfCandidate.HidingQueries

/-! Actual lazy-prefix caches and their associated syntactic query counts. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate

private theorem counted_step {α : Type} (query : World.Domain)
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

theorem lazy_cache_actual_count {α : Type} (compress : Compression)
    (program : OracleComp World α) (cache : Cache) (result : α × Cache)
    (present : result ∈ support (lazyRun compress program cache)) :
    ∃ calls, (result.1, calls) ∈ support (Hiding.counted program) ∧
      result.2.entries.length ≤ cache.entries.length + calls := by
  induction program using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    simp only [lazyRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
    subst result
    refine ⟨0, ?_, ?_⟩
    · change (value, (0 : Nat)) ∈ support (pure (value, (0 : Nat)))
      simp
    · change cache.entries.length ≤ cache.entries.length + 0
      omega
  | query_bind query next ih =>
    have expand : lazyRun compress ((liftM (World.query query) : OracleComp World _) >>= next) cache =
        (lazyHandler compress query).run cache >>= fun result => lazyRun compress (next result.1) result.2 := by
      simp [lazyRun, simulateQ_bind, StateT.run_bind]
    rw [expand] at present
    obtain ⟨⟨answer, middle⟩, reached, finished⟩ := (mem_support_bind_iff _ _ _).mp present
    obtain ⟨calls, counted, tail⟩ := ih answer middle result finished
    have advances : middle.entries.length ≤ cache.entries.length + Oracle.callCost query := by
      rcases query with coins | (input | (input | output))
      · simp only [lazyHandler, StateT.run_monadLift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at reached
        obtain ⟨coin, _, same⟩ := reached
        cases same
        rfl
      · simp only [lazyHandler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
        cases reached
        exact Nat.le_succ _
      · exact forward_cache_growth cache input (answer, middle) reached
      · exact inverse_cache_growth cache output (answer, middle) reached
    exact ⟨Oracle.callCost query+calls, counted_step query next answer (result.1, calls) counted, by omega⟩

theorem hiding_prefix_split {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) (compress : Compression)
    (prior : Hiding.HidingChallenge State openingSize × Cache)
    (reached : prior ∈ support (lazyRun compress adversary.choose (PermutationCache.empty Block))) :
    ∃ calls, calls ≤ budget ∧ prior.2.entries.length ≤ calls ∧
      ∀ root proof, QueryBounded (adversary.observe prior.1.aux root proof) (budget-calls) := by
  obtain ⟨calls, counted, length⟩ := lazy_cache_actual_count compress adversary.choose _ prior reached
  refine ⟨calls, (bounded (prior.1, calls) counted).1, ?_, ?_⟩
  · simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using length
  · intro root proof
    exact hiding_observe_query_bound adversary bounded (prior.1, calls) counted root proof

end TwoPermutationPrototype.Sampling
