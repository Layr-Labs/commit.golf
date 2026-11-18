import CommitGolfCandidate.ProjectedCollisionProduct

/-! Product-form bound for 240-bit compression collisions at 7q/2^124. With the
240-bit leaf collision term at 9q/2^124 the binding events sum to q/2^120. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

theorem small_budget_c (c N q m lo : ℝ) (c0 : 0 ≤ c) (hN : 2 ^ 238 ≤ N) (q1 : 1 ≤ q) (hq : q ≤ lo * 2 ^ 120)
    (hm : m ≤ q + 2 ^ 31) (m0 : 0 ≤ m) (lo1 : lo ≤ 1)
    (room : (lo + 1 / 2 ^ 50) * 2 ^ 240 ≤ 2 * c * N * (1 - 1 / 2 ^ 116)) :
    1 - Real.exp (-collisionExponent N m) ≤ c * (q / 2 ^ 120) := by
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
  have inner : lo * 2 ^ 120 + 2 ^ 63 ≤ 2 * c * (N - m) / 2 ^ 120 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left inner q0
  have eq : c * (q / 2 ^ 120) * (2 * (N - m)) = q * (2 * c * (N - m) / 2 ^ 120) := by ring
  linarith

theorem real_target_240 (q m : ℕ) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120) (hm : m ≤ q + 2 ^ 31) :
    1 - Real.exp (-collisionExponent (2 ^ 240) m) ≤ 7 / 16 * ((q : ℝ) / 2 ^ 120) := by
  have q1 : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qs : (q : ℝ) ≤ 2 ^ 120 := by exact_mod_cast small
  have mR : (m : ℝ) ≤ q + 2 ^ 31 := by exact_mod_cast hm
  have m0 : (0 : ℝ) ≤ m := by positivity
  have N : (2 : ℝ) ^ 238 ≤ 2 ^ 240 := by norm_num
  have piece : ∀ lo hi u : ℝ, lo * 2 ^ 120 ≤ q → q ≤ hi * 2 ^ 120 → 1 / 4 ≤ hi → hi ≤ 1 →
      2 ^ 239 / 2 ^ 240 * hi ^ 2 * (1001 / 1000) ≤ u → u ≤ ((64 : ℕ) : ℝ) →
      1 - (1 - u / ((64 : ℕ) : ℝ)) ^ 64 ≤ 7 / 16 * lo →
      1 - Real.exp (-collisionExponent (2 ^ 240) m) ≤ 7 / 16 * ((q : ℝ) / 2 ^ 120) := by
    intro lo hi u hl hh h4 h1 hu hu64 check
    exact interval_step _ _ _ lo u 64
      ((exponent_le _ _ _ hi N hh mR m0 (by linarith) h4 h1).trans hu) hu64 (by norm_num)
      (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num) check
  by_cases h0 : (q : ℝ) ≤ (87/100) * 2 ^ 120
  · exact small_budget_c (7/16) _ _ _ (87/100) (by norm_num) N q1 h0 mR m0 (by norm_num) (by norm_num)
  replace h0 := le_of_lt (not_le.mp h0)
  by_cases h1 : (q : ℝ) ≤ (95/100) * 2 ^ 120
  · exact piece (87/100) (95/100) (4518/10000) (by linarith) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h1 := le_of_lt (not_le.mp h1)
  exact piece (95/100) (1) (5005/10000) (by linarith) (by simpa using qs) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Product-form 240-bit compression collision bound: at most `7q/2^124`. -/
theorem projected_target_240 (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) (bounded : PublicQueryBound computation calls) :
    (prEvent ((fun result => ProjectedCollisionW 240 result.2) <$> (compressionRun permutation computation ∅))) ≤
      7 * (q : ENNReal) / 2 ^ 124 := by
  have room : calls < 2 ^ 240 := by omega
  have real := real_target_240 q calls positive small withReplay
  refine (projected_width_survival 240 (by omega) permutation computation calls bounded).trans ?_
  calc 1 - survival 240 0 calls ≤ 1 - ENNReal.ofReal (Real.exp (-collisionExponent (2 ^ 240) calls)) :=
        tsub_le_tsub_left (survival_ge_exp 240 calls room) 1
    _ = ENNReal.ofReal (1 - Real.exp (-collisionExponent (2 ^ 240) calls)) := by
        rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (7 / 16 * ((q : ℝ) / 2 ^ 120)) := ENNReal.ofReal_le_ofReal real
    _ = 7 * (q : ENNReal) / 2 ^ 124 := by
        rw [show (7 / 16 * ((q : ℝ) / 2 ^ 120)) = 7 * (q : ℝ) / 2 ^ 124 by ring,
          ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]

/-- The packed 240-bit projection is the width-generic one at `w = 240`. -/
theorem projected_collision_eq_w (cache : CompressionCache) :
    ProjectedCollision cache ↔ ProjectedCollisionW 240 cache := Iff.rfl

end CommitGolfCandidate
