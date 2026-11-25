import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingLeaf
import CommitGolfCandidate.CompressionSampling

/-! Connect the adaptive first stage to the fixed-cache hiding lemmas. The cache
and chosen challenge are sampled jointly; there is no independence assumption
between the adversary's choices and its earlier oracle answers. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingStagesDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-- The cache runner respects monadic sequencing (local copy, so the hiding proof does
not depend on the binding reduction's modules). -/
private theorem staged_compression_run_bind (permutation : Perm) {α β : Type}
    (first : OracleComp World α) (next : α → OracleComp World β) (cache : CompressionCache) :
    compressionRun permutation (first >>= next) cache = (do
      let (value, after) ← compressionRun permutation first cache
      compressionRun permutation (next value) after) := by
  simp [compressionRun, simulateQ_bind, StateT.run_bind]

/-- After any first stage, resample only the cells not fixed by its transcript.
This preserves the exact distribution of every oracle-aware continuation. -/
theorem staged_compression_sampling (permutation : Perm) {α β : Type}
    (first : OracleComp World α) (next : α → OracleComp World β) :
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (first >>= next)] =
    𝒟[do let (value, cache) ← compressionRun permutation first ∅
         let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next value)] := by
  rw [← compression_sampling_empty, staged_compression_run_bind, map_bind]
  apply _root_.evalDist_bind_congr
  intro result
  cases result with
  | mk value cache => exact compression_sampling_equivalence permutation (next value) cache

/-- A public-query budget bounds the number of populated compression inputs in
every reachable cache. Permutation queries can only reduce the available budget. -/
theorem compression_cache_covered (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (known : Finset CompressionSpec.Domain) (covered : ∀ key, cache key ≠ none → key ∈ known)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known.card + budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache known result with
  | pure value =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨known, by omega, covered⟩
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache known covered result reached
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget-1) := bounded.2
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          obtain ⟨keys, size, covers⟩ := ih answer (budget-1) (tails answer) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        | none =>
          rw [cached] at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          have nextCovered : ∀ key, (cache.cacheQuery input answer) key ≠ none →
              key ∈ insert input known := by
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covered key populated)
          obtain ⟨keys, size, covers⟩ := ih answer (budget-1) (tails answer)
            (cache.cacheQuery input answer) (insert input known) nextCovered result reached
          have inserted := Finset.card_insert_le input known
          exact ⟨keys, by omega, covers⟩
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget-1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        · rw [compression_run_inverse] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget-1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩

/-- In particular the first stage starts with no preloaded compression answers. -/
theorem first_stage_cache_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation ∅)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  have result := compression_cache_covered permutation computation budget bounded ∅ ∅
    (by simp) result reached
  simpa only [Finset.card_empty, Nat.zero_add] using result

end CommitGolfCandidate
