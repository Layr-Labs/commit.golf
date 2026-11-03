import CommitGolfCandidate.QueryBudget
import VCVio.OracleComp.QueryTracking.Birthday
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! Lazy compression sampling for the binding reduction. Private randomness stays
fresh, and both permutation directions use one fixed permutation. Only the
compression table is cached. The birthday induction follows VCVio's
`probEvent_cacheCollision_le_birthday_total_tight`, with separate cases for the
other oracle operations instead of treating them as compression queries. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

abbrev CompressionCache := CompressionSpec.QueryCache

/-- The two ideal primitives are independent. Conditioning on any permutation
leaves the compression primitive a random function. -/
def compressionHandler (permutation : Perm) : QueryImpl World (StateT CompressionCache ProbComp)
  | .inl coins => do
      let answer ← (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins))
      return answer
  | .inr (.inl input) => randomOracle input
  | .inr (.inr (.inl input)) => pure (permutation input)
  | .inr (.inr (.inr input)) => pure (permutation.symm input)

def compressionRun (permutation : Perm) {α : Type} (computation : OracleComp World α)
    (cache : CompressionCache) : ProbComp (α × CompressionCache) :=
  (simulateQ (compressionHandler permutation) computation).run cache

theorem compression_run_pure (permutation : Perm) {α : Type} (value : α) (cache : CompressionCache) :
    compressionRun permutation (pure value) cache = pure (value, cache) := by
  simp [compressionRun]

theorem compression_run_query_bind (permutation : Perm) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation ((liftM (World.query query) : OracleComp World _) >>= next) cache =
      (compressionHandler permutation query).run cache >>= fun result =>
        compressionRun permutation (next result.1) result.2 := by
  simp [compressionRun, simulateQ_bind, StateT.run_bind]

theorem compression_run_private (permutation : Perm) {α : Type} (coins : unifSpec.Domain)
    (next : unifSpec.Range coins → OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation ((liftM (World.query (.inl coins)) : OracleComp World _) >>= next) cache =
      (liftM (unifSpec.query coins) : ProbComp _) >>= fun answer =>
        compressionRun permutation (next answer) cache := by
  rw [compression_run_query_bind]
  simp [compressionHandler]

theorem compression_run_compress (permutation : Perm) {α : Type} (input : CompressionSpec.Domain)
    (next : CompressionSpec.Range input → OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= next) cache =
      match cache input with
      | some answer => compressionRun permutation (next answer) cache
      | none => ($ᵗ CompressionSpec.Range input) >>= fun answer =>
          compressionRun permutation (next answer) (cache.cacheQuery input answer) := by
  rw [compression_run_query_bind]
  change (randomOracle input).run cache >>= _ = _
  rw [randomOracle.run_eq]
  split <;> simp_all

theorem compression_run_permute (permutation : Perm) {α : Type} (input : BitVec PERMUTATION_WIDTH)
    (next : BitVec PERMUTATION_WIDTH → OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= next) cache =
      compressionRun permutation (next (permutation input)) cache := by
  rw [compression_run_query_bind]
  rfl

theorem compression_run_inverse (permutation : Perm) {α : Type} (input : BitVec PERMUTATION_WIDTH)
    (next : BitVec PERMUTATION_WIDTH → OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation ((liftM (World.query (.inr (.inr (.inr input)))) : OracleComp World _) >>= next) cache =
      compressionRun permutation (next (permutation.symm input)) cache := by
  rw [compression_run_query_bind]
  rfl

/-- With no collision yet, at most one fresh output per populated key can cause
one. VCVio's finite counting lemma applies without enumerating the huge domain. -/
theorem fresh_compression_collision_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ CacheHasCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    Pr[fun answer => CacheHasCollision (cache.cacheQuery input answer) |
      ($ᵗ CompressionSpec.Range input)] ≤ (keys.card : ENNReal) / 2 ^ 256 := by
  classical
  rw [probEvent_uniformSample]
  have count := card_responses_creating_cacheCollision_le (t := input) noCollision covers
  have cardinal : Fintype.card (CompressionSpec.Range input) = 2 ^ 256 := by
    change Fintype.card (BitVec 256) = 2 ^ 256
    simp
  rw [cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact_mod_cast count

/-- Adaptive birthday induction with unrestricted private coins and access to both
permutation directions. `known` bounds the populated keys in the starting cache. -/
theorem compression_collision_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ CacheHasCollision cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    Pr[fun result => CacheHasCollision result.2 | compressionRun permutation computation cache] ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [probEvent_pure, noCollision, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply probEvent_bind_le_of_forall_le
      intro answer _
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCollision covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∑ step ∈ Finset.range (budget - 1), ((known + step : Nat) : ENNReal) / 2 ^ 256) ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le budget 1))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCollision covered).trans smaller
        | none =>
          have fresh : Pr[fun answer => CacheHasCollision (cache.cacheQuery input answer) |
              ($ᵗ CompressionSpec.Range input)] ≤ (known : ENNReal) / 2 ^ 256 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_compression_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasCollision (cache.cacheQuery input answer) →
              Pr[fun result => CacheHasCollision result.2 |
                compressionRun permutation (next answer) (cache.cacheQuery input answer)] ≤
                ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256 := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := probEvent_bind_le_add
            (mx := ($ᵗ CompressionSpec.Range input))
            (my := fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (p := fun answer => ¬ CacheHasCollision (cache.cacheQuery input answer))
            (q := fun result => ¬ CacheHasCollision result.2)
            (ε₁ := (known : ENNReal) / 2 ^ 256)
            (ε₂ := ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 256)
            (by simpa only [not_not] using fresh)
            (by simpa only [not_not] using continuation)
          simp only [not_not] at combined
          apply combined.trans_eq
          conv_rhs => rw [show budget = (budget - 1) + 1 from by omega]
          rw [Finset.sum_range_succ']
          simp only [Nat.add_zero]
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro step _
          rw [show known + 1 + step = known + (step + 1) from by omega]
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller
        · rw [compression_run_inverse]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller

/-- Tight birthday bound for the compression cache, even when the adversary also
uses fresh private coins and the fixed ideal permutation in both directions. -/
theorem compression_collision_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    Pr[fun result => CacheHasCollision result.2 | compressionRun permutation computation ∅] ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) := by
  have estimate := compression_collision_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; simp at impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 256))

end CommitGolfCandidate
