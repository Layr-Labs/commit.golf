import CommitGolfCandidate.CompressionROM

/-! Product-form birthday bound for collisions in the low `w` bits of
compression replies.

The union bound `m(m-1)/2^(w+1)` exceeds one near `m ≈ 2^120` once `w < 240`.
This file proves the non-union bound `1 - ∏_{i<m} (1 - i/2^w)` by the same
lazy-sampling induction: a fresh reply collides with probability `p ≤ k/2^w`,
and otherwise the run continues from a collision-free cache with one more key,
so the event has probability at most `p + (1-p)(1-S) ≤ 1 - (1-k/2^w)S`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

set_option maxRecDepth 4096

section Width
variable (w : Nat)

abbrev WidthSpec := BitVec 512 →ₒ BitVec w

def lowBits (value : BitVec 256) : BitVec w := value.extractLsb' 0 w

def projectCacheW (cache : CompressionCache) : (WidthSpec w).QueryCache :=
  ⟨fun key => (cache key).map (lowBits w)⟩

def ProjectedCollisionW (cache : CompressionCache) : Prop := CacheHasCollision (projectCacheW w cache)

private theorem project_update_w (cache : CompressionCache) (key : BitVec 512) (value : BitVec 256) :
    projectCacheW w (cache.cacheQuery key value) =
      (projectCacheW w cache).cacheQuery key (lowBits w value) := by
  apply QueryCache.ext
  intro k
  by_cases same : k = key
  · subst k
    rw [QueryCache.cacheQuery_self]
    change Option.map (lowBits w) ((cache.cacheQuery key value) key) = some _
    rw [QueryCache.cacheQuery_self cache key value]
    rfl
  · rw [QueryCache.cacheQuery_of_ne (projectCacheW w cache) (lowBits w value) same]
    exact congrArg (Option.map (lowBits w)) (QueryCache.cacheQuery_of_ne cache value same)

private def joinDigestW (hw : w ≤ 256) : BitVec (256 - w) × BitVec w ≃ BitVec 256 where
  toFun := fun p => (p.1 ++ p.2).cast (by omega)
  invFun := fun value => (value.extractLsb' w (256 - w), lowBits w value)
  left_inv := by
    rintro ⟨high, low⟩
    refine Prod.ext ?_ ?_
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
      omega
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [lowBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]
  right_inv := by
    intro value
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [lowBits, BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases low : i < w
    · simp [low]
    · have h1 : i - w < 256 - w := by omega
      have h2 : w + (i - w) = i := by omega
      simp [low, h1, h2]

/-- A fresh full-width reply creates a low-`w` collision with probability at
most one in `2^w` per populated key, even after its high bits are disclosed. -/
theorem fresh_projected_collision_bound_w (hw : w ≤ 256) (cache : CompressionCache)
    (input : CompressionSpec.Domain) (keys : Finset CompressionSpec.Domain)
    (noCollision : ¬ ProjectedCollisionW w cache)
    (covers : ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun answer => ProjectedCollisionW w (cache.cacheQuery input answer)) <$>
      ($ᵗ CompressionSpec.Range input))) ≤ (keys.card : ENNReal) / 2 ^ w := by
  classical
  change Pr{let value ← $ᵗ BitVec 256}[ProjectedCollisionW w (cache.cacheQuery input value)] ≤ _
  rw [← SampleableType.prEvent_uniformSample_equiv (joinDigestW w hw)]
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro high
  have projectedCovers : ∀ key, projectCacheW w cache key ≠ none → key ∈ keys := by
    intro key populated
    apply covers
    intro missing
    exact populated (by change Option.map (lowBits w) (cache key) = none; rw [missing]; rfl)
  have count := card_responses_creating_cacheCollision_le (t := input)
    (cache₀ := projectCacheW w cache) noCollision projectedCovers
  have charge (low : BitVec w) :
      ProjectedCollisionW w (cache.cacheQuery input (joinDigestW w hw (high, low))) =
        CacheHasCollision ((projectCacheW w cache).cacheQuery input low) := by
    unfold ProjectedCollisionW
    apply congrArg CacheHasCollision
    refine (project_update_w w cache input (joinDigestW w hw (high, low))).trans ?_
    have extract : lowBits w (joinDigestW w hw (high, low)) = low :=
      congrArg Prod.snd ((joinDigestW w hw).left_inv (high, low))
    rw [extract]
  simp_rw [charge]
  rw [SampleableType.prEvent_uniformSample]
  have denom : Fintype.card (BitVec w) = 2^w := by simp
  rw [denom, Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr count

/-- Probability that `b` fresh replies, starting from `k` populated keys, stay
collision free (the exact product, as an `ENNReal` lower bound). -/
noncomputable def survival (k b : Nat) : ENNReal :=
  ∏ i ∈ Finset.range b, (1 - ((k + i : Nat) : ENNReal) / 2 ^ w)

theorem survival_le_one (k b : Nat) : survival w k b ≤ 1 :=
  Finset.prod_le_one (fun _ _ => tsub_le_self)

theorem survival_succ (k b : Nat) :
    survival w k (b + 1) = (1 - (k : ENNReal) / 2 ^ w) * survival w (k + 1) b := by
  unfold survival
  rw [Finset.prod_range_succ', mul_comm]
  exact congrArg₂ (· * ·) (by simp)
    (Finset.prod_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by omega])

theorem survival_pred_le (k b : Nat) : survival w k b ≤ survival w k (b - 1) := by
  rcases b with _ | b
  · exact le_rfl
  · unfold survival
    rw [Finset.prod_range_succ, show b + 1 - 1 = b by omega]
    exact mul_le_of_le_one_right' tsub_le_self

private theorem step_algebra {p a y : ENNReal} (pa : p ≤ a) (p1 : p ≤ 1) (y1 : y ≤ 1) :
    p + (1 - y) * (1 - p) ≤ 1 - (1 - a) * y := by
  have xfin : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have expand : (1 - y) * (1 - p) = 1 * (1 - p) - y * (1 - p) :=
    ENNReal.sub_mul (fun _ _ => xfin)
  rw [expand, one_mul]
  have yx : y * (1 - p) ≤ 1 - p := mul_le_of_le_one_left' y1
  rw [add_comm p, ENNReal.sub_add_eq_add_sub yx (ne_top_of_le_ne_top xfin yx), tsub_add_cancel_of_le p1]
  apply tsub_le_tsub_left
  calc (1 - a) * y ≤ (1 - p) * y := by gcongr
    _ = y * (1 - p) := mul_comm _ _

/-- Adaptive product-form birthday induction with unrestricted private coins
and access to both permutation directions. -/
theorem projected_width_survival_from_cache (hw : w ≤ 256) (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget known : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (noCollision : ¬ ProjectedCollisionW w cache)
    (covered : ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known ∧
      ∀ key, cache key ≠ none → key ∈ keys) :
    (prEvent ((fun result => ProjectedCollisionW w result.2) <$>
      (compressionRun permutation computation cache))) ≤ 1 - survival w known budget := by
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
      have smaller : 1 - survival w known (budget - 1) ≤ 1 - survival w known budget :=
        tsub_le_tsub_left (survival_pred_le w known budget) 1
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          exact (ih answer (budget - 1) known (tails answer) cache noCollision covered).trans smaller
        | none =>
          have fresh : (prEvent ((fun answer => ProjectedCollisionW w (cache.cacheQuery input answer)) <$>
              (($ᵗ CompressionSpec.Range input)))) ≤ (known : ENNReal) / 2 ^ w := by
            obtain ⟨keys, size, covers⟩ := covered
            exact (fresh_projected_collision_bound_w w hw cache input keys noCollision covers).trans
              (ENNReal.div_le_div_right (Nat.cast_le.mpr size) _)
          have continuation : ∀ answer ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ ProjectedCollisionW w (cache.cacheQuery input answer) →
              (prEvent ((fun result => ProjectedCollisionW w result.2) <$>
                (compressionRun permutation (next answer) (cache.cacheQuery input answer)))) ≤
                1 - survival w (known + 1) (budget - 1) := by
            intro answer _ safe
            apply ih answer (budget - 1) (known + 1) (tails answer) _ safe
            obtain ⟨keys, size, covers⟩ := covered
            refine ⟨insert input keys, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covers key populated)
          have combined := prEvent_bind_le_prEvent_add_mul_prEvent_not_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun answer => compressionRun permutation (next answer) (cache.cacheQuery input answer))
            (fun answer => ProjectedCollisionW w (cache.cacheQuery input answer))
            (fun result => ProjectedCollisionW w result.2) continuation
          rw [prEvent_not_eq_one_sub] at combined
          refine combined.trans ?_
          rw [show budget = (budget - 1) + 1 from by omega, survival_succ, Nat.add_sub_cancel]
          exact step_algebra fresh (prEvent_le_one _) (survival_le_one w _ _)
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller
        · rw [compression_run_inverse]
          exact (ih _ (budget - 1) known (tails _) cache noCollision covered).trans smaller

theorem projected_width_survival (hw : w ≤ 256) (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat) (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result => ProjectedCollisionW w result.2) <$> (compressionRun permutation computation ∅))) ≤
      1 - survival w 0 budget :=
  projected_width_survival_from_cache w hw permutation computation budget 0 bounded ∅
    (by rintro ⟨_, _, _, _, _, impossible, _⟩; change none = some _ at impossible; cases impossible)
    ⟨∅, by simp, fun key populated => (populated rfl).elim⟩

end Width

/-! ## Real lower bound on the survival product -/

/-- The collision exponent `m(m-1)/(2(N-m))`. -/
noncomputable def collisionExponent (N m : ℝ) : ℝ := m * (m - 1) / 2 / (N - m)

private theorem factor_lower (N m i : ℝ) (hi : 0 ≤ i) (him : i < m) (hmN : m < N) :
    Real.exp (-(i / (N - m))) ≤ 1 - i / N := by
  have Npos : 0 < N := by linarith
  have gap : 0 < N - i := by linarith
  have gapm : 0 < N - m := by linarith
  have mono : i / (N - i) ≤ i / (N - m) := div_le_div_of_nonneg_left hi gapm (by linarith)
  have grow := Real.add_one_le_exp (i / (N - i))
  have ratio : i / (N - i) + 1 = N / (N - i) := by field_simp; ring
  calc Real.exp (-(i / (N - m))) ≤ Real.exp (-(i / (N - i))) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / Real.exp (i / (N - i)) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (N / (N - i)) := by
        apply one_div_le_one_div_of_le (by positivity)
        rw [← ratio]; exact grow
    _ = 1 - i / N := by field_simp

theorem survival_ge_exp (w m : Nat) (room : m < 2 ^ w) :
    ENNReal.ofReal (Real.exp (-collisionExponent (2 ^ w) m)) ≤ survival w 0 m := by
  have roomR : (m : ℝ) < 2 ^ w := by exact_mod_cast room
  have factor (i : Nat) (hi : i ∈ Finset.range m) :
      (1 - ((0 + i : Nat) : ENNReal) / 2 ^ w) = ENNReal.ofReal (1 - (i : ℝ) / 2 ^ w) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, Nat.zero_add]
  unfold survival
  rw [Finset.prod_congr rfl factor, ← ENNReal.ofReal_prod_of_nonneg]
  · apply ENNReal.ofReal_le_ofReal
    have sum : collisionExponent (2 ^ w) m = ∑ i ∈ Finset.range m, (i : ℝ) / (2 ^ w - m) := by
      rw [← Finset.sum_div]
      unfold collisionExponent
      congr 1
      have gauss := Finset.sum_range_id_mul_two m
      rcases Nat.eq_zero_or_pos m with zero | pos
      · subst zero; simp
      · have cast : ((∑ i ∈ Finset.range m, i : Nat) : ℝ) * 2 = (m : ℝ) * ((m : ℝ) - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, gauss, Nat.cast_mul, Nat.cast_sub pos, Nat.cast_one]
        push_cast at cast
        linarith
    rw [sum, ← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
    intro i hi
    exact factor_lower _ _ _ (by positivity) (by exact_mod_cast Finset.mem_range.mp hi) roomR
  · intro i hi
    have : (i : ℝ) < 2 ^ w := lt_trans (by exact_mod_cast Finset.mem_range.mp hi) roomR
    rw [sub_nonneg, div_le_one (by positivity)]
    exact this.le

/-! ## Arithmetic for the binding target -/

/-- An interval of budgets where `exp(-s) ≥ exp(-u) ≥ (1-u/n)^n` meets the target. -/
theorem interval_step (s x c lo u : ℝ) (n : ℕ) (hs : s ≤ u) (hu : u ≤ n) (hn : 0 < n)
    (hx : lo ≤ x) (hc : 0 ≤ c) (check : 1 - (1 - u / n) ^ n ≤ c * lo) :
    1 - Real.exp (-s) ≤ c * x := by
  have npos : (0 : ℝ) < n := by exact_mod_cast hn
  have base : 0 ≤ 1 - u / n := by rw [sub_nonneg, div_le_one npos]; exact hu
  have step : (1 - u / n) ^ n ≤ Real.exp (-u) := by
    have single : 1 - u / n ≤ Real.exp (-(u / n)) := by linarith [Real.add_one_le_exp (-(u / n))]
    calc (1 - u / n) ^ n ≤ Real.exp (-(u / n)) ^ n := pow_le_pow_left₀ base single n
      _ = Real.exp (-u) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have mono : Real.exp (-u) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- The collision exponent in terms of the normalized budget bound `hi`. -/
theorem exponent_le (N q m hi : ℝ) (hN : 2 ^ 238 ≤ N) (hq : q ≤ hi * 2 ^ 120)
    (hm : m ≤ q + 2 ^ 31) (m0 : 0 ≤ m) (q0 : 0 ≤ q) (hlo : 1 / 4 ≤ hi) (hhi : hi ≤ 1) :
    collisionExponent N m ≤ 2 ^ 239 / N * hi ^ 2 * (1001 / 1000) := by
  have mUp : m ≤ hi * 2 ^ 120 + 2 ^ 31 := by linarith
  have mSmall : m ≤ 2 ^ 121 := by nlinarith
  have gap : N - 2 ^ 121 ≤ N - m := by linarith
  have far : (2 : ℝ) ^ 121 < 2 ^ 238 := by norm_num
  have gapPos : 0 < N - 2 ^ 121 := by linarith
  unfold collisionExponent
  rw [div_div, div_le_iff₀ (by nlinarith)]
  have sq : m * (m - 1) ≤ (hi * 2 ^ 120 + 2 ^ 31) ^ 2 := by nlinarith
  have expand : (hi * 2 ^ 120 + 2 ^ 31) ^ 2 ≤ hi ^ 2 * 2 ^ 240 * (1 + 1 / 2 ^ 80) := by nlinarith
  have Nfactor : 2 ^ 239 / N * (2 * (N - m)) ≥ 2 ^ 240 * (1 - 1 / 2 ^ 116) := by
    have Npos : 0 < N := by linarith
    rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ Npos]
    nlinarith
  have hi2 : 0 ≤ hi ^ 2 := sq_nonneg hi
  have key : hi ^ 2 * 2 ^ 240 * (1 + 1 / 2 ^ 80) ≤
      hi ^ 2 * (1001 / 1000) * (2 ^ 240 * (1 - 1 / 2 ^ 116)) := by
    have c : (1 : ℝ) + 1 / 2 ^ 80 ≤ (1001 / 1000) * (1 - 1 / 2 ^ 116) := by norm_num
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left Nfactor (by positivity : 0 ≤ hi ^ 2 * (1001 / 1000))
  nlinarith

/-- Small budgets: `1 - exp(-s) ≤ s`, and `s` is linear in the budget below `lo`. -/
theorem small_budget (N q m lo : ℝ) (hN : 2 ^ 238 ≤ N) (q1 : 1 ≤ q) (hq : q ≤ lo * 2 ^ 120)
    (hm : m ≤ q + 2 ^ 31) (m0 : 0 ≤ m) (lo1 : lo ≤ 1)
    (room : (lo + 1 / 2 ^ 50) * 2 ^ 240 ≤ 15 / 8 * N * (1 - 1 / 2 ^ 116)) :
    1 - Real.exp (-collisionExponent N m) ≤ 15 / 16 * (q / 2 ^ 120) := by
  have q0 : 0 ≤ q := by linarith
  have mSmall : m ≤ 2 ^ 121 := by nlinarith
  have Npos : 0 < N := by linarith
  have far : (2 : ℝ) ^ 121 < 2 ^ 238 := by norm_num
  have gapPos : 0 < N - m := by linarith
  have lin : 1 - Real.exp (-collisionExponent N m) ≤ collisionExponent N m := by
    linarith [Real.add_one_le_exp (-collisionExponent N m)]
  refine lin.trans ?_
  unfold collisionExponent
  rw [div_div, div_le_iff₀ (by linarith)]
  have mm : m * (m - 1) ≤ m * m := by nlinarith
  have m2 : m * m ≤ (q + 2 ^ 31) * (q + 2 ^ 31) := mul_self_le_mul_self m0 hm
  have qq : q * q ≤ q * (lo * 2 ^ 120) := mul_le_mul_of_nonneg_left hq q0
  have lin2 : 2 * 2 ^ 31 * q + 2 ^ 62 ≤ q * 2 ^ 63 := by nlinarith
  have sq : m * (m - 1) ≤ q * (lo * 2 ^ 120 + 2 ^ 63) := by nlinarith
  have gap : N * (1 - 1 / 2 ^ 116) ≤ N - m := by
    have : (2 : ℝ) ^ 121 ≤ N * (1 / 2 ^ 116) := by
      have h : (2 : ℝ) ^ 121 ≤ 2 ^ 238 * (1 / 2 ^ 116) := by norm_num
      nlinarith
    linarith
  have inner : lo * 2 ^ 120 + 2 ^ 63 ≤ 15 / 8 * (N - m) / 2 ^ 120 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left inner q0
  have eq : 15 / 16 * (q / 2 ^ 120) * (2 * (N - m)) = q * (15 / 8 * (N - m) / 2 ^ 120) := by ring
  linarith

theorem real_target_239 (q m : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (hm : m ≤ q + 2 ^ 31) :
    1 - Real.exp (-collisionExponent (2 ^ 239) m) ≤ 15 / 16 * ((q : ℝ) / 2 ^ 120) := by
  have q1 : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qs : (q : ℝ) ≤ 2 ^ 120 := by exact_mod_cast small
  have mR : (m : ℝ) ≤ q + 2 ^ 31 := by exact_mod_cast hm
  have m0 : (0 : ℝ) ≤ m := by positivity
  have N : (2 : ℝ) ^ 238 ≤ 2 ^ 239 := by norm_num
  have piece : ∀ lo hi u : ℝ, lo * 2 ^ 120 ≤ q → q ≤ hi * 2 ^ 120 → 1 / 4 ≤ hi → hi ≤ 1 →
      2 ^ 239 / 2 ^ 239 * hi ^ 2 * (1001 / 1000) ≤ u → u ≤ ((64 : ℕ) : ℝ) →
      1 - (1 - u / ((64 : ℕ) : ℝ)) ^ 64 ≤ 15 / 16 * lo →
      1 - Real.exp (-collisionExponent (2 ^ 239) m) ≤ 15 / 16 * ((q : ℝ) / 2 ^ 120) := by
    intro lo hi u hl hh h4 h1 hu hu64 check
    exact interval_step _ _ _ lo u 64
      ((exponent_le _ _ _ hi N hh mR m0 (by linarith) h4 h1).trans hu) hu64 (by norm_num)
      (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num) check
  by_cases h0 : (q : ℝ) ≤ (93/100) * 2 ^ 120
  · exact small_budget _ _ _ (93/100) N q1 h0 mR m0 (by norm_num) (by norm_num)
  exact piece (93/100) (1) (1001/1000) (by linarith) (by simpa using qs) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem real_target_238 (q m : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (hm : m ≤ q + 2 ^ 31) :
    1 - Real.exp (-collisionExponent (2 ^ 238) m) ≤ 15 / 16 * ((q : ℝ) / 2 ^ 120) := by
  have q1 : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qs : (q : ℝ) ≤ 2 ^ 120 := by exact_mod_cast small
  have mR : (m : ℝ) ≤ q + 2 ^ 31 := by exact_mod_cast hm
  have m0 : (0 : ℝ) ≤ m := by positivity
  have N : (2 : ℝ) ^ 238 ≤ 2 ^ 238 := by norm_num
  have piece : ∀ lo hi u : ℝ, lo * 2 ^ 120 ≤ q → q ≤ hi * 2 ^ 120 → 1 / 4 ≤ hi → hi ≤ 1 →
      2 ^ 239 / 2 ^ 238 * hi ^ 2 * (1001 / 1000) ≤ u → u ≤ ((64 : ℕ) : ℝ) →
      1 - (1 - u / ((64 : ℕ) : ℝ)) ^ 64 ≤ 15 / 16 * lo →
      1 - Real.exp (-collisionExponent (2 ^ 238) m) ≤ 15 / 16 * ((q : ℝ) / 2 ^ 120) := by
    intro lo hi u hl hh h4 h1 hu hu64 check
    exact interval_step _ _ _ lo u 64
      ((exponent_le _ _ _ hi N hh mR m0 (by linarith) h4 h1).trans hu) hu64 (by norm_num)
      (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num) check
  by_cases h0 : (q : ℝ) ≤ (23/50) * 2 ^ 120
  · exact small_budget _ _ _ (23/50) N q1 h0 mR m0 (by norm_num) (by norm_num)
  by_cases h1 : (q : ℝ) ≤ (13/25) * 2 ^ 120
  · exact piece (23/50) (13/25) (169169/312500) (by linarith) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h1 := le_of_lt (not_le.mp h1)
  by_cases h2 : (q : ℝ) ≤ (11/20) * 2 ^ 120
  · exact piece (13/25) (11/20) (121121/200000) (by linarith) h2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h2 := le_of_lt (not_le.mp h2)
  by_cases h3 : (q : ℝ) ≤ (23/40) * 2 ^ 120
  · exact piece (11/20) (23/40) (529529/800000) (by linarith) h3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h3 := le_of_lt (not_le.mp h3)
  by_cases h4 : (q : ℝ) ≤ (3/5) * 2 ^ 120
  · exact piece (23/40) (3/5) (9009/12500) (by linarith) h4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h4 := le_of_lt (not_le.mp h4)
  by_cases h5 : (q : ℝ) ≤ (5/8) * 2 ^ 120
  · exact piece (3/5) (5/8) (1001/1280) (by linarith) h5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h5 := le_of_lt (not_le.mp h5)
  by_cases h6 : (q : ℝ) ≤ (129/200) * 2 ^ 120
  · exact piece (5/8) (129/200) (16657641/20000000) (by linarith) h6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h6 := le_of_lt (not_le.mp h6)
  by_cases h7 : (q : ℝ) ≤ (133/200) * 2 ^ 120
  · exact piece (129/200) (133/200) (17706689/20000000) (by linarith) h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h7 := le_of_lt (not_le.mp h7)
  by_cases h8 : (q : ℝ) ≤ (137/200) * 2 ^ 120
  · exact piece (133/200) (137/200) (18787769/20000000) (by linarith) h8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h8 := le_of_lt (not_le.mp h8)
  by_cases h9 : (q : ℝ) ≤ (7/10) * 2 ^ 120
  · exact piece (137/200) (7/10) (49049/50000) (by linarith) h9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h9 := le_of_lt (not_le.mp h9)
  by_cases h10 : (q : ℝ) ≤ (143/200) * 2 ^ 120
  · exact piece (7/10) (143/200) (20469449/20000000) (by linarith) h10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h10 := le_of_lt (not_le.mp h10)
  by_cases h11 : (q : ℝ) ≤ (73/100) * 2 ^ 120
  · exact piece (143/200) (73/100) (5334329/5000000) (by linarith) h11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h11 := le_of_lt (not_le.mp h11)
  by_cases h12 : (q : ℝ) ≤ (149/200) * 2 ^ 120
  · exact piece (73/100) (149/200) (22223201/20000000) (by linarith) h12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h12 := le_of_lt (not_le.mp h12)
  by_cases h13 : (q : ℝ) ≤ (19/25) * 2 ^ 120
  · exact piece (149/200) (19/25) (361361/312500) (by linarith) h13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h13 := le_of_lt (not_le.mp h13)
  by_cases h14 : (q : ℝ) ≤ (31/40) * 2 ^ 120
  · exact piece (19/25) (31/40) (961961/800000) (by linarith) h14 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h14 := le_of_lt (not_le.mp h14)
  by_cases h15 : (q : ℝ) ≤ (157/200) * 2 ^ 120
  · exact piece (31/40) (157/200) (24673649/20000000) (by linarith) h15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h15 := le_of_lt (not_le.mp h15)
  by_cases h16 : (q : ℝ) ≤ (159/200) * 2 ^ 120
  · exact piece (157/200) (159/200) (25306281/20000000) (by linarith) h16 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h16 := le_of_lt (not_le.mp h16)
  by_cases h17 : (q : ℝ) ≤ (41/50) * 2 ^ 120
  · exact piece (159/200) (41/50) (1682681/1250000) (by linarith) h17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h17 := le_of_lt (not_le.mp h17)
  by_cases h18 : (q : ℝ) ≤ (21/25) * 2 ^ 120
  · exact piece (41/50) (21/25) (441441/312500) (by linarith) h18 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h18 := le_of_lt (not_le.mp h18)
  by_cases h19 : (q : ℝ) ≤ (43/50) * 2 ^ 120
  · exact piece (21/25) (43/50) (1850849/1250000) (by linarith) h19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h19 := le_of_lt (not_le.mp h19)
  by_cases h20 : (q : ℝ) ≤ (179/200) * 2 ^ 120
  · exact piece (43/50) (179/200) (32073041/20000000) (by linarith) h20 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h20 := le_of_lt (not_le.mp h20)
  by_cases h21 : (q : ℝ) ≤ (189/200) * 2 ^ 120
  · exact piece (179/200) (189/200) (35756721/20000000) (by linarith) h21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h21 := le_of_lt (not_le.mp h21)
  exact piece (189/200) (1) (1001/500) (by linarith) (by simpa using qs) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CommitGolfCandidate

namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- Product-form binding target at 238 or 239 bits: the low-`w` compression
collision probability is at most `15q/2^124`, leaving `q/2^124` for other events. -/
theorem projected_width_target (w : Nat) (hw : w = 238 ∨ w = 239) (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) (bounded : PublicQueryBound computation calls) :
    (prEvent ((fun result => ProjectedCollisionW w result.2) <$> (compressionRun permutation computation ∅))) ≤
      15 * (q : ENNReal) / 2 ^ 124 := by
  have room : calls < 2 ^ w := by
    rcases hw with rfl | rfl <;> omega
  have real : 1 - Real.exp (-collisionExponent (2 ^ w) calls) ≤ 15 / 16 * ((q : ℝ) / 2 ^ 120) := by
    rcases hw with rfl | rfl
    · exact real_target_238 q calls positive small withReplay
    · exact real_target_239 q calls positive small withReplay
  refine (projected_width_survival w (by omega) permutation computation calls bounded).trans ?_
  calc 1 - survival w 0 calls ≤ 1 - ENNReal.ofReal (Real.exp (-collisionExponent (2 ^ w) calls)) :=
        tsub_le_tsub_left (survival_ge_exp w calls room) 1
    _ = ENNReal.ofReal (1 - Real.exp (-collisionExponent (2 ^ w) calls)) := by
        rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (15 / 16 * ((q : ℝ) / 2 ^ 120)) := ENNReal.ofReal_le_ofReal real
    _ = 15 * (q : ENNReal) / 2 ^ 124 := by
        rw [show (15 / 16 * ((q : ℝ) / 2 ^ 120)) = 15 * (q : ℝ) / 2 ^ 124 by ring,
          ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]

end CommitGolfCandidate

