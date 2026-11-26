import CommitGolfCandidate.QueryBudget
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.Birthday
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! Lazy compression sampling for the binding reduction. Private randomness stays
fresh, and both permutation directions use one fixed permutation. Only the
compression table is cached. The birthday induction follows VCVio's
`prEvent_cacheCollision_le_birthday_total_tight`, with separate cases for the
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
    (prEvent ((fun answer => CacheHasCollision (cache.cacheQuery input answer)) <$> (($ᵗ CompressionSpec.Range input)))) ≤ (keys.card : ENNReal) / 2 ^ 256 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
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
    (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation computation cache))) ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 256 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noCollision, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
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
          have fresh : (prEvent ((fun answer => CacheHasCollision (cache.cacheQuery input answer)) <$> (($ᵗ CompressionSpec.Range input)))) ≤ (known : ENNReal) / 2 ^ 256 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_compression_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasCollision (cache.cacheQuery input answer) →
              (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
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
          have combined := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => CacheHasCollision (cache.cacheQuery input answer))
            (fun result => CacheHasCollision result.2) continuation).trans
              (add_le_add fresh le_rfl)
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
    (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation computation ∅))) ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) := by
  have estimate := compression_collision_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; simp at impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 256))

/-! ### Low-240-bit collisions

Selective truncation stores heap parents of height at least 3 truncated to their low 240 bits.
Binding then reduces to two distinct cached inputs whose replies agree on the low
240 bits. The same adaptive birthday induction applies with `2^240` in place of
`2^256`: each fresh reply hits one of at most `2^16` full replies per populated key. -/

/-- Two distinct cached inputs whose replies agree on their low 240 bits. -/
def CacheHasLowCollision (cache : CompressionCache) : Prop :=
  ∃ (t₁ t₂ : CompressionSpec.Domain) (u₁ u₂ : BitVec COMPRESSION_OUTPUT_LENGTH), t₁ ≠ t₂ ∧
    cache t₁ = some u₁ ∧ cache t₂ = some u₂ ∧ u₁.extractLsb' 0 240 = u₂.extractLsb' 0 240

/-- At most `2^16` 256-bit replies share given low 240 bits. -/
theorem bd_card_low_fiber_le (low : BitVec 240) :
    (Finset.univ.filter (fun reply : BitVec COMPRESSION_OUTPUT_LENGTH =>
      reply.extractLsb' 0 240 = low)).card ≤ 2 ^ 16 := by
  classical
  have injective : Set.InjOn (fun reply : BitVec COMPRESSION_OUTPUT_LENGTH => reply.extractLsb' 240 16)
      (Finset.univ.filter (fun reply : BitVec COMPRESSION_OUTPUT_LENGTH =>
        reply.extractLsb' 0 240 = low) : Set (BitVec COMPRESSION_OUTPUT_LENGTH)) := by
    intro a ha b hb same
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
    apply BitVec.eq_of_getLsbD_eq
    intro bit hbit
    simp only [COMPRESSION_OUTPUT_LENGTH] at hbit
    by_cases lowBit : bit < 240
    · have := congrArg (fun x : BitVec 240 => x.getLsbD bit) (ha.trans hb.symm)
      simpa [BitVec.getLsbD_extractLsb', lowBit] using this
    · have := congrArg (fun x : BitVec 16 => x.getLsbD (bit - 240)) same
      have shift : 240 + (bit - 240) = bit := by omega
      have small : bit - 240 < 16 := by omega
      simpa [BitVec.getLsbD_extractLsb', small, shift] using this
  have := Finset.card_le_card_of_injOn (fun reply : BitVec COMPRESSION_OUTPUT_LENGTH => reply.extractLsb' 240 16)
    (t := (Finset.univ : Finset (BitVec 16))) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) injective
  simpa using this

open Classical in
/-- Counting form: without a prior low collision, at most `2^16` replies per
populated key create one. -/
theorem bd_card_low_responses_le (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ CacheHasLowCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (Finset.univ.filter (fun reply : CompressionSpec.Range input =>
      CacheHasLowCollision (cache.cacheQuery input reply))).card ≤ keys.card * 2 ^ 16 := by
  let fiber : CompressionSpec.Domain → Finset (BitVec COMPRESSION_OUTPUT_LENGTH) := fun key =>
    match cache key with
    | some value => Finset.univ.filter (fun reply : BitVec COMPRESSION_OUTPUT_LENGTH =>
        reply.extractLsb' 0 240 = (value : BitVec COMPRESSION_OUTPUT_LENGTH).extractLsb' 0 240)
    | none => ∅
  have fiberSize : ∀ key ∈ keys, (fiber key).card ≤ 2 ^ 16 := by
    intro key _
    simp only [fiber]
    split
    · exact bd_card_low_fiber_le _
    · simp
  have hit : ∀ (reply : BitVec COMPRESSION_OUTPUT_LENGTH) (key : CompressionSpec.Domain)
      (value : BitVec COMPRESSION_OUTPUT_LENGTH), cache key = some value →
      reply.extractLsb' 0 240 = value.extractLsb' 0 240 → ∃ key ∈ keys, reply ∈ fiber key := by
    intro reply key value stored lowSame
    refine ⟨key, covers key (by rw [stored]; simp), ?_⟩
    simp only [fiber, stored]
    simpa using lowSame
  have inUnion : (Finset.univ.filter (fun reply : CompressionSpec.Range input =>
      CacheHasLowCollision (cache.cacheQuery input reply)) : Finset (BitVec COMPRESSION_OUTPUT_LENGTH)) ⊆
      keys.biUnion fiber := by
    intro reply member
    obtain ⟨t₁, t₂, u₁, u₂, hne, h1, h2, same⟩ := (Finset.mem_filter.mp member).2
    rw [Finset.mem_biUnion]
    by_cases first : t₁ = input
    · subst first
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h1
      subst h1
      exact hit _ t₂ u₂ (by rwa [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hne)] at h2) same
    · by_cases second : t₂ = input
      · subst second
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at h2
        subst h2
        exact hit _ t₁ u₁ (by rwa [QueryCache.cacheQuery_of_ne _ _ first] at h1) same.symm
      · exact (noCollision ⟨t₁, t₂, u₁, u₂, hne, by rwa [QueryCache.cacheQuery_of_ne _ _ first] at h1,
          by rwa [QueryCache.cacheQuery_of_ne _ _ second] at h2, same⟩).elim
  calc _ ≤ (keys.biUnion fiber).card := Finset.card_le_card inUnion
    _ ≤ ∑ key ∈ keys, (fiber key).card := Finset.card_biUnion_le
    _ ≤ ∑ _key ∈ keys, 2 ^ 16 := Finset.sum_le_sum fiberSize
    _ = keys.card * 2 ^ 16 := by simp

theorem bd_fresh_low_collision_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ CacheHasLowCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun answer => CacheHasLowCollision (cache.cacheQuery input answer)) <$>
      (($ᵗ CompressionSpec.Range input)))) ≤ (keys.card : ENNReal) / 2 ^ 240 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have count := bd_card_low_responses_le cache input keys noCollision covers
  have cardinal : Fintype.card (CompressionSpec.Range input) = 2 ^ 256 := by
    change Fintype.card (BitVec 256) = 2 ^ 256
    simp
  rw [cardinal]
  have countCast : ((Finset.univ.filter (fun answer : CompressionSpec.Range input =>
      CacheHasLowCollision (cache.cacheQuery input answer))).card : ENNReal) ≤
      (keys.card : ENNReal) * 2 ^ 16 := by
    exact_mod_cast count
  calc _ ≤ ((keys.card : ENNReal) * 2 ^ 16) / ((2 ^ 256 : Nat) : ENNReal) :=
        ENNReal.div_le_div_right countCast _
    _ = (keys.card : ENNReal) / 2 ^ 240 := by
        rw [show ((2 ^ 256 : Nat) : ENNReal) = 2 ^ 240 * 2 ^ 16 by rw [← pow_add]; norm_num]
        exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- Adaptive low-240 birthday induction; same structure as
`compression_collision_bound_from_cache`. -/
theorem bd_low_collision_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ CacheHasLowCollision cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun result => CacheHasLowCollision result.2) <$> (compressionRun permutation computation cache))) ≤
      ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, noCollision, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro answer _
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCollision covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∑ step ∈ Finset.range (budget - 1), ((known + step : Nat) : ENNReal) / 2 ^ 240) ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le budget 1))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCollision covered).trans smaller
        | none =>
          have fresh : (prEvent ((fun answer => CacheHasLowCollision (cache.cacheQuery input answer)) <$>
              (($ᵗ CompressionSpec.Range input)))) ≤ (known : ENNReal) / 2 ^ 240 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (bd_fresh_low_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHasLowCollision (cache.cacheQuery input answer) →
              (prEvent ((fun result => CacheHasLowCollision result.2) <$> (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
                ∑ step ∈ Finset.range (budget - 1), ((known + 1 + step : Nat) : ENNReal) / 2 ^ 240 := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => CacheHasLowCollision (cache.cacheQuery input answer))
            (fun result => CacheHasLowCollision result.2) continuation).trans
              (add_le_add fresh le_rfl)
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

/-- Birthday bound for low-240 collisions in the compression cache: `q(q-1)/2^241`. -/
theorem bd_low_collision_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result => CacheHasLowCollision result.2) <$> (compressionRun permutation computation ∅))) ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) := by
  have estimate := bd_low_collision_bound_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; simp at impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 240))


end CommitGolfCandidate
