import CommitGolfCandidate.QueryBudget
import CommitGolfCandidate.S6Tree
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

/-! ### Truncated replies

Internal tree nodes keep the low 240 bits of a compression reply (`s6Trunc`). The same adaptive
birthday induction bounds collisions of truncated replies: a fresh reply collides with one of
`k` populated keys for at most `k * 2^16` of the `2^256` answers. -/

/-- Two different compression inputs whose replies agree on their low 240 bits. -/
def TruncCacheHasCollision (cache : CompressionCache) : Prop :=
  ∃ (first second : CompressionSpec.Domain) (u₁ : CompressionSpec.Range first)
    (u₂ : CompressionSpec.Range second),
    first ≠ second ∧ cache first = some u₁ ∧ cache second = some u₂ ∧ s6Trunc u₁ = s6Trunc u₂

/-- At most `2^16` digests have given low 240 bits. -/
theorem trunc_fiber_card (target : BitVec 256) :
    (Finset.univ.filter fun answer : BitVec 256 => s6Trunc answer = target).card ≤ 2 ^ 16 := by
  classical
  have count := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter fun answer : BitVec 256 => s6Trunc answer = target)
    (t := (Finset.univ : Finset (BitVec 16))) (fun answer => BitVec.ofNat 16 (answer.toNat / 2 ^ 240))
    (by intro _ _; simp) (by
      intro first firstMember second secondMember same
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at firstMember secondMember
      have low := congrArg BitVec.toNat (firstMember.trans secondMember.symm)
      have high := congrArg BitVec.toNat same
      simp only [s6Trunc, BitVec.toNat_ofNat] at low high
      have firstSmall : first.toNat < 2 ^ 256 := first.isLt
      have secondSmall : second.toNat < 2 ^ 256 := second.isLt
      apply BitVec.eq_of_toNat_eq
      omega)
  simpa using count

open Classical in
/-- With no truncated collision yet, a fresh reply creates one for at most `2^16` answers per
populated key. -/
theorem trunc_responses_card (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ TruncCacheHasCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (Finset.univ.filter fun answer : CompressionSpec.Range input =>
      TruncCacheHasCollision (cache.cacheQuery input answer)).card ≤ keys.card * 2 ^ 16 := by
  have inside : (Finset.univ.filter fun answer : CompressionSpec.Range input =>
        TruncCacheHasCollision (cache.cacheQuery input answer)) ⊆
      keys.biUnion fun key => Finset.univ.filter fun answer : CompressionSpec.Range input =>
        ∃ stored : CompressionSpec.Range key, cache key = some stored ∧
          s6Trunc answer = s6Trunc stored := by
    intro answer member
    obtain ⟨first, second, u₁, u₂, different, firstStored, secondStored, equal⟩ :=
      (Finset.mem_filter.mp member).2
    have hit : ∀ (key : CompressionSpec.Domain) (stored : CompressionSpec.Range key),
        cache key = some stored → s6Trunc answer = s6Trunc stored →
        answer ∈ keys.biUnion fun key => Finset.univ.filter fun answer : CompressionSpec.Range input =>
          ∃ stored : CompressionSpec.Range key, cache key = some stored ∧
            s6Trunc answer = s6Trunc stored := by
      intro key stored present same
      refine Finset.mem_biUnion.mpr ⟨key, covers key (by rw [present]; simp), ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨stored, present, same⟩
    by_cases firstInput : first = input
    · subst firstInput
      have secondOther : second ≠ first := fun same => different same.symm
      rw [QueryCache.cacheQuery_self] at firstStored
      rw [QueryCache.cacheQuery_of_ne _ _ secondOther] at secondStored
      have same : u₁ = answer := (Option.some.inj firstStored).symm
      subst same
      exact hit second u₂ secondStored equal
    · by_cases secondInput : second = input
      · subst secondInput
        rw [QueryCache.cacheQuery_self] at secondStored
        rw [QueryCache.cacheQuery_of_ne _ _ firstInput] at firstStored
        have same : u₂ = answer := (Option.some.inj secondStored).symm
        subst same
        exact hit first u₁ firstStored equal.symm
      · rw [QueryCache.cacheQuery_of_ne _ _ firstInput] at firstStored
        rw [QueryCache.cacheQuery_of_ne _ _ secondInput] at secondStored
        exact absurd ⟨first, second, u₁, u₂, different, firstStored, secondStored, equal⟩
          noCollision
  refine (Finset.card_le_card inside).trans
    (Finset.card_biUnion_le_card_mul _ _ _ fun key _ => ?_)
  change (Finset.univ.filter fun answer : BitVec 256 =>
      ∃ stored : CompressionSpec.Range key, cache key = some stored ∧
        s6Trunc answer = s6Trunc stored).card ≤ 2 ^ 16
  rcases Option.eq_none_or_eq_some (cache key) with absent | ⟨stored, present⟩
  · have empty : (Finset.univ.filter fun answer : BitVec 256 =>
        ∃ stored : CompressionSpec.Range key, cache key = some stored ∧
          s6Trunc answer = s6Trunc stored) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro answer - ⟨stored, present, -⟩
      rw [absent] at present
      simp at present
    exact (Finset.card_eq_zero.mpr empty).trans_le (Nat.zero_le _)
  · refine (Finset.card_le_card
      (t := Finset.univ.filter fun answer : BitVec 256 => s6Trunc answer = s6Trunc stored)
      ?_).trans (trunc_fiber_card (s6Trunc stored))
    intro answer member
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
    obtain ⟨other, otherPresent, same⟩ := member
    rw [present] at otherPresent
    have equal : stored = other := Option.some.inj otherPresent
    subst equal
    exact same

/-- With no truncated collision yet, a fresh answer creates one with probability at most
`k / 2^240` for `k` populated keys. -/
theorem fresh_trunc_collision_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ TruncCacheHasCollision cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun answer => TruncCacheHasCollision (cache.cacheQuery input answer)) <$>
      (($ᵗ CompressionSpec.Range input)))) ≤ (keys.card : ENNReal) / 2 ^ 240 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have count := trunc_responses_card cache input keys noCollision covers
  have cardinal : Fintype.card (CompressionSpec.Range input) = 2 ^ 256 := by
    change Fintype.card (BitVec 256) = 2 ^ 256
    simp
  rw [cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have sixteenNonzero : (2 : ENNReal) ^ 16 ≠ 0 := pow_ne_zero _ two_ne_zero
  have sixteenFinite : (2 : ENNReal) ^ 16 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have scaled : ((keys.card * 2 ^ 16 : Nat) : ENNReal) / 2 ^ 256 =
      (keys.card : ENNReal) / 2 ^ 240 := by
    rw [show (2 : ENNReal) ^ 256 = 2 ^ 240 * 2 ^ 16 by rw [← pow_add], Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_div_mul_right _ _ sixteenNonzero sixteenFinite
  rw [← scaled]
  apply ENNReal.div_le_div_right
  exact_mod_cast count

/-- Adaptive birthday induction for truncated replies, with unrestricted private coins and both
permutation directions. `known` bounds the populated keys in the starting cache. -/
theorem trunc_compression_collision_bound_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ TruncCacheHasCollision cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun result => TruncCacheHasCollision result.2) <$>
      (compressionRun permutation computation cache))) ≤
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
      exact ih answer budget known
        (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCollision covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      have smaller : (∑ step ∈ Finset.range (budget - 1),
            ((known + step : Nat) : ENNReal) / 2 ^ 240) ≤
          ∑ step ∈ Finset.range budget, ((known + step : Nat) : ENNReal) / 2 ^ 240 :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le budget 1))
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCollision covered).trans
            smaller
        | none =>
          have fresh : (prEvent ((fun answer => TruncCacheHasCollision
              (cache.cacheQuery input answer)) <$> (($ᵗ CompressionSpec.Range input)))) ≤
              (known : ENNReal) / 2 ^ 240 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_trunc_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ TruncCacheHasCollision (cache.cacheQuery input answer) →
              (prEvent ((fun result => TruncCacheHasCollision result.2) <$>
                (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
                ∑ step ∈ Finset.range (budget - 1),
                  ((known + 1 + step : Nat) : ENNReal) / 2 ^ 240 := by
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
            (fun answer => TruncCacheHasCollision (cache.cacheQuery input answer))
            (fun result => TruncCacheHasCollision result.2) continuation).trans
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

/-- **Truncated-reply birthday bound.** Two different compression inputs whose replies agree on
their low 240 bits appear in the lazy cache with probability at most
`budget (budget - 1) / (2 * 2^240)`, with private coins and the fixed ideal permutation in both
directions available. -/
theorem trunc_compression_collision_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result => TruncCacheHasCollision result.2) <$>
      (compressionRun permutation computation ∅))) ≤
      ((budget * (budget - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) := by
  have estimate := trunc_compression_collision_bound_from_cache permutation computation budget 0
    bounded ∅ (by rintro ⟨_, _, _, _, _, impossible, _⟩; simp at impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add, div_eq_mul_inv] at estimate
  exact estimate.trans_eq (ENNReal.gauss_sum_inv_eq budget ((2 : ENNReal) ^ 240))

end CommitGolfCandidate
