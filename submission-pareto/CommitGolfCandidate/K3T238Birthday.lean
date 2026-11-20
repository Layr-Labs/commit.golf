import CommitGolfCandidate.K3T238Witness

/-! Product-form birthday bound for collisions in the low 238 bits of compression replies.
The sampled oracle still returns the full 256 bits to every adversary. The adaptive part is
proved as a lower bound on the probability that no projected collision appears; the real part
bounds the product `∏_{i<N} (1 - i/M)` from below by an exponential. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 4096

abbrev Projected238Spec := BitVec 512 →ₒ BitVec 238

def projectCache238 (cache : CompressionCache) : Projected238Spec.QueryCache :=
  ⟨fun key => (cache key).map low238⟩

def ProjectedCollision238 (cache : CompressionCache) : Prop := CacheHasCollision (projectCache238 cache)

/-! ## Real part -/

private theorem exp_neg_le_one_sub {y : ℝ} (nonneg : 0 ≤ y) (half : y ≤ 1 / 2) :
    Real.exp (-(y + y ^ 2)) ≤ 1 - y := by
  have tnonneg : 0 ≤ y + y ^ 2 := by positivity
  have quad := Real.quadratic_le_exp_of_nonneg tnonneg
  have cubic : y + y ^ 2 + y ^ 3 ≤ 1 := by
    nlinarith [mul_nonneg nonneg (sub_nonneg.mpr half),
      mul_nonneg (mul_nonneg nonneg nonneg) (sub_nonneg.mpr half)]
  have poly : 1 ≤ (1 - y) * (1 + (y + y ^ 2) + (y + y ^ 2) ^ 2 / 2) := by
    have expand : (1 - y) * (1 + (y + y ^ 2) + (y + y ^ 2) ^ 2 / 2) - 1 =
        y ^ 2 / 2 * (1 - y - y ^ 2 - y ^ 3) := by ring
    have slack : 0 ≤ y ^ 2 / 2 * (1 - y - y ^ 2 - y ^ 3) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have key : 1 ≤ (1 - y) * Real.exp (y + y ^ 2) :=
    poly.trans (mul_le_mul_of_nonneg_left quad (by linarith))
  have cancel : Real.exp (-(y + y ^ 2)) * Real.exp (y + y ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have positive : 0 ≤ Real.exp (-(y + y ^ 2)) := (Real.exp_pos _).le
  calc Real.exp (-(y + y ^ 2)) = Real.exp (-(y + y ^ 2)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(y + y ^ 2)) * ((1 - y) * Real.exp (y + y ^ 2)) :=
      mul_le_mul_of_nonneg_left key positive
    _ = (1 - y) * (Real.exp (-(y + y ^ 2)) * Real.exp (y + y ^ 2)) := by ring
    _ = 1 - y := by rw [cancel, mul_one]

private theorem sum_range_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_range_sq_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have grow : ((n : ℝ) + 1) ^ 3 / 3 = (n : ℝ) ^ 3 / 3 + (n : ℝ) ^ 2 + n + 1 / 3 := by ring
    rw [grow]
    linarith

/-- S9-R F6, real form: for `2N ≤ M`, `∏_{i<N} (1 - i/M) ≥ exp(-(N(N-1)/(2M) + N^3/(3M^2)))`. -/
theorem birthday_exp_le_product (M N : Nat) (hM : 0 < M) (room : 2 * N ≤ M) :
    Real.exp (-((N : ℝ) * ((N : ℝ) - 1) / (2 * M) + (N : ℝ) ^ 3 / (3 * (M : ℝ) ^ 2))) ≤
      ∏ i ∈ Finset.range N, (1 - (i : ℝ) / M) := by
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have roomR : 2 * (N : ℝ) ≤ M := by exact_mod_cast room
  have total : ∑ i ∈ Finset.range N, ((i : ℝ) / M + ((i : ℝ) / M) ^ 2) ≤
      (N : ℝ) * ((N : ℝ) - 1) / (2 * M) + (N : ℝ) ^ 3 / (3 * (M : ℝ) ^ 2) := by
    have linear : ∑ i ∈ Finset.range N, (i : ℝ) / M = (N : ℝ) * ((N : ℝ) - 1) / (2 * M) := by
      rw [← Finset.sum_div, sum_range_cast, div_div]
    have squares : ∑ i ∈ Finset.range N, ((i : ℝ) / M) ^ 2 =
        (∑ i ∈ Finset.range N, (i : ℝ) ^ 2) / (M : ℝ) ^ 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => div_pow _ _ _)
    have bound : (∑ i ∈ Finset.range N, (i : ℝ) ^ 2) / (M : ℝ) ^ 2 ≤
        (N : ℝ) ^ 3 / 3 / (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (sum_range_sq_le N) (by positivity)
    have reshape : (N : ℝ) ^ 3 / 3 / (M : ℝ) ^ 2 = (N : ℝ) ^ 3 / (3 * (M : ℝ) ^ 2) := by
      rw [div_div]
    rw [Finset.sum_add_distrib, linear, squares]
    linarith
  calc Real.exp (-((N : ℝ) * ((N : ℝ) - 1) / (2 * M) + (N : ℝ) ^ 3 / (3 * (M : ℝ) ^ 2)))
      ≤ Real.exp (-(∑ i ∈ Finset.range N, ((i : ℝ) / M + ((i : ℝ) / M) ^ 2))) :=
        Real.exp_le_exp.mpr (neg_le_neg total)
    _ = ∏ i ∈ Finset.range N, Real.exp (-((i : ℝ) / M + ((i : ℝ) / M) ^ 2)) := by
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
    _ ≤ ∏ i ∈ Finset.range N, (1 - (i : ℝ) / M) := by
        apply Finset.prod_le_prod₀
        · intro i _
          exact (Real.exp_pos _).le
        · intro i hi
          have below : i + 1 ≤ N := Finset.mem_range.mp hi
          have belowR : (i : ℝ) + 1 ≤ N := by exact_mod_cast below
          have half : (i : ℝ) / M ≤ 1 / 2 := by
            rw [div_le_iff₀ hMpos]
            linarith
          exact exp_neg_le_one_sub (by positivity) half

/-! ## Adaptive part -/

private theorem project238_update (cache : CompressionCache) (key : BitVec 512) (value : BitVec 256) :
    projectCache238 (cache.cacheQuery key value) = (projectCache238 cache).cacheQuery key (low238 value) := by
  apply QueryCache.ext
  intro k
  by_cases same : k = key
  · subst k
    rw [QueryCache.cacheQuery_self]
    change Option.map low238 ((cache.cacheQuery key value) key) = some _
    rw [QueryCache.cacheQuery_self cache key value]
    rfl
  · rw [QueryCache.cacheQuery_of_ne (projectCache238 cache) (low238 value) same]
    exact congrArg (Option.map low238) (QueryCache.cacheQuery_of_ne cache value same)

private def joinDigest238 : BitVec 18 × BitVec 238 ≃ BitVec 256 where
  toFun := fun ⟨high, low⟩ => high ++ low
  invFun := fun value => (value.extractLsb' 238 18, low238 value)
  left_inv := by
    rintro ⟨high, low⟩
    exact Prod.ext (BitVec.extractLsb'_append_eq_left (a := high) (b := low))
      (BitVec.extractLsb'_append_eq_right (a := high) (b := low))
  right_inv := by
    intro value
    unfold low238
    exact BitVec.extractLsb'_append_extractLsb' (w := 18) (len := 238)

/-- Each fresh full-width answer creates a collision in the low 238 bits with probability at
most one in 2^238 per previously queried input, even after its high bits are disclosed. -/
theorem fresh_projected238_collision_bound (cache : CompressionCache) (input : CompressionSpec.Domain)
    (keys : Finset CompressionSpec.Domain) (noCollision : ¬ ProjectedCollision238 cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun answer => ProjectedCollision238 (cache.cacheQuery input answer)) <$>
      ($ᵗ CompressionSpec.Range input))) ≤ (keys.card : ENNReal) / 2 ^ 238 := by
  classical
  change Pr{let value ← $ᵗ BitVec 256}[ProjectedCollision238 (cache.cacheQuery input value)] ≤ _
  rw [← SampleableType.prEvent_uniformSample_equiv joinDigest238]
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro high
  have projectedCovers : ∀ key, projectCache238 cache key ≠ none → key ∈ keys := by
    intro key populated
    apply covers
    intro missing
    exact populated (by change Option.map low238 (cache key) = none; rw [missing]; rfl)
  have count := card_responses_creating_cacheCollision_le (t := input)
    (cache₀ := projectCache238 cache) noCollision projectedCovers
  have charge (low : BitVec 238) :
      ProjectedCollision238 (cache.cacheQuery input (joinDigest238 (high, low))) =
        CacheHasCollision ((projectCache238 cache).cacheQuery input low) := by
    unfold ProjectedCollision238
    apply congrArg CacheHasCollision
    refine (project238_update cache input (joinDigest238 (high, low))).trans ?_
    have extract : low238 (joinDigest238 (high, low)) = low :=
      BitVec.extractLsb'_append_eq_right (a := high) (b := low)
    rw [extract]
  simp_rw [charge]
  rw [SampleableType.prEvent_uniformSample]
  have denom : Fintype.card (BitVec 238) = 2^238 := by simp
  rw [denom, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr count

/-- Dropping the last factor of the survival product can only increase it. -/
private theorem survival_drop (known budget : Nat) :
    ∏ step ∈ Finset.range budget, (1 - ((known + step : Nat) : ENNReal) / 2 ^ 238) ≤
      ∏ step ∈ Finset.range (budget - 1), (1 - ((known + step : Nat) : ENNReal) / 2 ^ 238) :=
  Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono (Nat.sub_le budget 1))
    (fun _ _ _ => tsub_le_self)

/-- The first factor of the survival product, followed by the product for one more known key. -/
private theorem survival_split (known budget : Nat) (positive : 1 ≤ budget) :
    ∏ step ∈ Finset.range budget, (1 - ((known + step : Nat) : ENNReal) / 2 ^ 238) =
      (1 - (known : ENNReal) / 2 ^ 238) *
        ∏ step ∈ Finset.range (budget - 1), (1 - ((known + 1 + step : Nat) : ENNReal) / 2 ^ 238) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by omega⟩
  have shift : ∀ step ∈ Finset.range rest,
      (1 - ((known + (step + 1) : Nat) : ENNReal) / 2 ^ 238) =
        (1 - ((known + 1 + step : Nat) : ENNReal) / 2 ^ 238) := by
    intro step _
    have same : known + (step + 1) = known + 1 + step := by omega
    rw [same]
  rw [Finset.prod_range_succ', Nat.add_sub_cancel, Finset.prod_congr rfl shift, Nat.add_zero]
  exact mul_comm _ _

/-- Adaptive survival induction with unrestricted private coins and access to both permutation
directions: the probability that no low-238 collision appears is at least the birthday product.
`known` bounds the populated keys in the starting cache. -/
theorem projected238_safe_from_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ ProjectedCollision238 cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    ∏ step ∈ Finset.range budget, (1 - ((known + step : Nat) : ENNReal) / 2 ^ 238) ≤
      prEvent ((fun result => ¬ ProjectedCollision238 result.2) <$>
        (compressionRun permutation computation cache)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget known cache with
  | pure value =>
    rw [compression_run_pure, prEvent_pure,
      ite_eq_left (show ¬ ProjectedCollision238 (value, cache).2 from noCollision)]
    exact Finset.prod_le_one (fun _ _ => tsub_le_self)
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      refine le_prEvent_bind_of_forall_le _ (OracleComp.prEvent_true_eq_one _) _ _ ?_
      intro answer
      exact ih answer budget known (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache noCollision covered
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (survival_drop known budget).trans
            (ih answer (budget - 1) known (tails answer) cache noCollision covered)
        | none =>
          have fresh : (prEvent ((fun answer => ProjectedCollision238 (cache.cacheQuery input answer)) <$>
              ($ᵗ CompressionSpec.Range input))) ≤ (known : ENNReal) / 2 ^ 238 := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_projected238_collision_bound cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have freshSafe : 1 - (known : ENNReal) / 2 ^ 238 ≤
              prEvent ((fun answer => ¬ ProjectedCollision238 (cache.cacheQuery input answer)) <$>
                ($ᵗ CompressionSpec.Range input)) := by
            rw [OracleComp.prEvent_not_eq_one_sub]
            exact tsub_le_tsub_left fresh 1
          have continuation : ∀ answer, ¬ ProjectedCollision238 (cache.cacheQuery input answer) →
              ∏ step ∈ Finset.range (budget - 1),
                  (1 - ((known + 1 + step : Nat) : ENNReal) / 2 ^ 238) ≤
                prEvent ((fun result => ¬ ProjectedCollision238 result.2) <$>
                  (compressionRun permutation (next answer) (cache.cacheQuery input answer))) := by
            intro answer safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := mul_le_prEvent_bind_of_forall ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => ¬ ProjectedCollision238 (cache.cacheQuery input answer))
            (fun result => ¬ ProjectedCollision238 result.2) freshSafe continuation
          rw [survival_split known budget positive]
          exact combined
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (survival_drop known budget).trans
            (ih _ (budget - 1) known (tails _) cache noCollision covered)
        · rw [compression_run_inverse]
          exact (survival_drop known budget).trans
            (ih _ (budget - 1) known (tails _) cache noCollision covered)

/-- Adaptive product-form birthday on the low 238 bits (same setting as `projected_collision_bound`:
private coins and both permutation directions free, budget counts every public query). -/
theorem projected238_collision_product (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    prEvent ((fun result => ProjectedCollision238 result.2) <$> compressionRun permutation computation ∅) ≤
      1 - ∏ step ∈ Finset.range budget, (1 - (step : ENNReal) / 2 ^ 238) := by
  have safe := projected238_safe_from_cache permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; change none = some _ at impossible; cases impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩
  simp only [Nat.zero_add] at safe
  have split := prEvent_add_prEvent_not_eq_prEvent_true (compressionRun permutation computation ∅)
    (fun result => ProjectedCollision238 result.2)
  rw [OracleComp.prEvent_true_eq_one] at split
  calc prEvent ((fun result => ProjectedCollision238 result.2) <$> compressionRun permutation computation ∅)
      = 1 - prEvent ((fun result => ¬ ProjectedCollision238 result.2) <$>
          compressionRun permutation computation ∅) :=
        ENNReal.eq_sub_of_add_eq (prEvent_ne_top _) split
    _ ≤ 1 - ∏ step ∈ Finset.range budget, (1 - (step : ENNReal) / 2 ^ 238) :=
        tsub_le_tsub_left safe 1

/-- The S9-R F6 statement at n = 238 (`2^(n+1) = 2^239`, `3·4^n = 3·4^238`). -/
theorem projected238_collision_exp (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget)
    (room : budget ≤ 2 ^ 237) :
    prEvent ((fun result => ProjectedCollision238 result.2) <$> compressionRun permutation computation ∅) ≤
      ENNReal.ofReal (1 - Real.exp (-((budget : ℝ) * ((budget : ℝ) - 1) / 2 ^ 239 +
        (budget : ℝ) ^ 3 / (3 * 4 ^ 238)))) := by
  refine (projected238_collision_product permutation computation budget bounded).trans ?_
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  refine tsub_le_tsub_left ?_ 1
  have roomN : 2 * budget ≤ 2 ^ 238 :=
    (Nat.mul_le_mul_left 2 room).trans_eq (pow_succ' 2 237).symm
  have real := birthday_exp_le_product (2 ^ 238) budget (Nat.two_pow_pos 238) roomN
  have castM : ((2 ^ 238 : ℕ) : ℝ) = (2 : ℝ) ^ 238 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have twice : (2 : ℝ) * 2 ^ 238 = 2 ^ 239 := (pow_succ' (2 : ℝ) 238).symm
  have square : ((2 : ℝ) ^ 238) ^ 2 = 4 ^ 238 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact congrArg (· ^ 238) (by norm_num : (2 : ℝ) ^ 2 = 4)
  rw [castM, twice, square] at real
  have below : ∀ i ∈ Finset.range budget, (i : ℝ) ≤ 2 ^ 238 := by
    intro i hi
    have small : i ≤ 2 ^ 238 :=
      ((Finset.mem_range.mp hi).le.trans room).trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    have cast : ((i : ℕ) : ℝ) ≤ ((2 ^ 238 : ℕ) : ℝ) := Nat.cast_le.mpr small
    rwa [castM] at cast
  have nonneg : ∀ i ∈ Finset.range budget, (0 : ℝ) ≤ 1 - (i : ℝ) / 2 ^ 238 := by
    intro i hi
    exact sub_nonneg.mpr ((div_le_one₀ (by positivity)).mpr (below i hi))
  have twoPow : ENNReal.ofReal ((2 : ℝ) ^ 238) = 2 ^ 238 := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have factor : ∀ i ∈ Finset.range budget,
      ENNReal.ofReal (1 - (i : ℝ) / 2 ^ 238) = 1 - (i : ENNReal) / 2 ^ 238 := by
    intro i _
    have quotient : ENNReal.ofReal ((i : ℝ) / 2 ^ 238) = (i : ENNReal) / 2 ^ 238 := by
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 238), ENNReal.ofReal_natCast,
        twoPow]
    rw [ENNReal.ofReal_sub 1 (by positivity : (0 : ℝ) ≤ (i : ℝ) / 2 ^ 238), ENNReal.ofReal_one,
      quotient]
  calc ENNReal.ofReal (Real.exp (-((budget : ℝ) * ((budget : ℝ) - 1) / 2 ^ 239 +
        (budget : ℝ) ^ 3 / (3 * 4 ^ 238))))
      ≤ ENNReal.ofReal (∏ i ∈ Finset.range budget, (1 - (i : ℝ) / 2 ^ 238)) :=
        ENNReal.ofReal_le_ofReal real
    _ = ∏ i ∈ Finset.range budget, ENNReal.ofReal (1 - (i : ℝ) / 2 ^ 238) :=
        ENNReal.ofReal_prod_of_nonneg nonneg
    _ = ∏ i ∈ Finset.range budget, (1 - (i : ENNReal) / 2 ^ 238) :=
        Finset.prod_congr rfl factor

end CommitGolfCandidate
