import Mathlib

/-!
# The 238-bit tree term fits its share of the binding budget

With `N = calls ≤ q + 2^31` compression-side queries and `s = N(N-1)/2^239 + N^3/(3·4^238)` (the product-form
birthday exponent at 238 bits), `1 - exp(-s) ≤ 255·q/2^128` for every `1 ≤ q ≤ 2^120`. In `x = q/2^120`:
`s ≤ 2(x + 2^-89)^2 + (x + 2^-89)^3/2^117`.

* `x ≤ 7/16`: `1 - exp(-s) ≤ s ≤ (7/8 + 2^-56)·x`.
* `7/16 ≤ x ≤ 1`: nine intervals `[a, b]`; on each, `s ≤ 2b^2 + 2^-20` and
  `exp(-t) ≥ (1 - t/16)^16 ≥ 1 - (255/256)·a` (exact rational checks, `t238_budget.py` part 2).
-/

namespace CommitGolfCandidate

set_option exponentiation.threshold 600

/-- `exp(-t) ≥ (1 - t/k)^k` for `0 < k` and `t ≤ k`. -/
theorem exp_neg_ge_one_sub_pow (t : ℝ) (k : ℕ) (hk : 0 < k) (ht : t ≤ k) :
    (1 - t / k) ^ k ≤ Real.exp (-t) := by
  have kPos : (0 : ℝ) < k := by exact_mod_cast hk
  have kNe : (k : ℝ) ≠ 0 := kPos.ne'
  have base : 0 ≤ 1 - t / k := by
    have : t / k ≤ 1 := (div_le_one kPos).2 ht
    linarith
  have step : 1 - t / k ≤ Real.exp (-(t / k)) := by
    have := Real.add_one_le_exp (-(t / k))
    linarith
  have power : Real.exp (-(t / k)) ^ k = Real.exp (-t) := by
    rw [← Real.exp_nat_mul]
    apply congrArg Real.exp
    field_simp
  exact (pow_le_pow_left₀ base step k).trans_eq power

/-- One interval of the upper range. -/
theorem t238_interval (a b x s : ℝ) (lower : a ≤ x) (upper : x ≤ b) (nonneg : 0 ≤ x)
    (exponent : s ≤ 2 * x ^ 2 + 1 / 2 ^ 20) (fits : 2 * b ^ 2 + 1 / 2 ^ 20 ≤ 16)
    (check : 1 - 255 / 256 * a ≤ (1 - (2 * b ^ 2 + 1 / 2 ^ 20) / 16) ^ 16) :
    1 - Real.exp (-s) ≤ 255 / 256 * x := by
  have square : x ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ nonneg upper 2
  have toB : s ≤ 2 * b ^ 2 + 1 / 2 ^ 20 := by linarith
  have mono : Real.exp (-(2 * b ^ 2 + 1 / 2 ^ 20)) ≤ Real.exp (-s) :=
    Real.exp_le_exp.2 (by linarith)
  have power := exp_neg_ge_one_sub_pow (2 * b ^ 2 + 1 / 2 ^ 20) 16 (by norm_num) (by exact_mod_cast fits)
  simp only [Nat.cast_ofNat] at power
  linarith

/-- The exponent in `x = q/2^120` and `y = calls/2^120`. -/
theorem t238_exponent_le (y : ℝ) (nonneg : 0 ≤ y) :
    (y * 2 ^ 120) * ((y * 2 ^ 120) - 1) / 2 ^ 239 + (y * 2 ^ 120) ^ 3 / (3 * 4 ^ 238) ≤
      2 * y ^ 2 + y ^ 3 / 2 ^ 117 := by
  have same : (y * 2 ^ 120) * ((y * 2 ^ 120) - 1) / 2 ^ 239 + (y * 2 ^ 120) ^ 3 / (3 * 4 ^ 238) =
      2 * y ^ 2 - y / 2 ^ 119 + y ^ 3 / (3 * 2 ^ 116) := by ring
  rw [same]
  have cube : 0 ≤ y ^ 3 := pow_nonneg nonneg 3
  have third : y ^ 3 / (3 * 2 ^ 116) ≤ y ^ 3 / 2 ^ 117 :=
    div_le_div_of_nonneg_left cube (by positivity) (by norm_num)
  have linear : 0 ≤ y / 2 ^ 119 := by positivity
  linarith

/-- The tree term at 238 bits, in reals. -/
theorem t238_tree_real (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q + 2^31) :
    1 - Real.exp (-((calls : ℝ) * ((calls : ℝ) - 1) / 2 ^ 239 + (calls : ℝ) ^ 3 / (3 * 4 ^ 238))) ≤
      255 * (q : ℝ) / 2^128 := by
  set x : ℝ := (q : ℝ) / 2 ^ 120 with hx
  set y : ℝ := (calls : ℝ) / 2 ^ 120 with hy
  have callsEq : (calls : ℝ) = y * 2 ^ 120 := by rw [hy]; field_simp
  have target : 255 * (q : ℝ) / 2 ^ 128 = 255 / 256 * x := by rw [hx]; ring
  rw [target, callsEq]
  set s : ℝ := (y * 2 ^ 120) * ((y * 2 ^ 120) - 1) / 2 ^ 239 + (y * 2 ^ 120) ^ 3 / (3 * 4 ^ 238) with hs
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qTop : (q : ℝ) ≤ 2 ^ 120 := by exact_mod_cast small
  have replayReal : (calls : ℝ) ≤ (q : ℝ) + 2 ^ 31 := by exact_mod_cast replayed
  have xLow : 1 / 2 ^ 120 ≤ x := by rw [hx]; exact div_le_div_of_nonneg_right qOne (by positivity)
  have xTop : x ≤ 1 := by rw [hx]; exact (div_le_one (by positivity)).2 qTop
  have x0 : 0 ≤ x := le_trans (by positivity) xLow
  have y0 : 0 ≤ y := by rw [hy]; positivity
  have yx : y ≤ x + 1 / 2 ^ 89 := by
    rw [hy, hx]
    have : ((q : ℝ) + 2 ^ 31) / 2 ^ 120 = (q : ℝ) / 2 ^ 120 + 1 / 2 ^ 89 := by ring
    rw [← this]
    exact div_le_div_of_nonneg_right replayReal (by positivity)
  have sBound : s ≤ 2 * y ^ 2 + y ^ 3 / 2 ^ 117 := t238_exponent_le y y0
  have ySq : y ^ 2 ≤ (x + 1 / 2 ^ 89) ^ 2 := pow_le_pow_left₀ y0 yx 2
  have dSmall : (1 : ℝ) / 2 ^ 89 ≤ 2 ^ 31 * x := by
    have := mul_le_mul_of_nonneg_left xLow (by positivity : (0 : ℝ) ≤ 2 ^ 31)
    have same : (2 : ℝ) ^ 31 * (1 / 2 ^ 120) = 1 / 2 ^ 89 := by norm_num
    linarith
  rcases le_or_gt x (7 / 16) with low | high
  · -- 1 - exp(-s) ≤ s ≤ (255/256) x
    have linearExp : 1 - Real.exp (-s) ≤ s := by
      have := Real.add_one_le_exp (-s)
      linarith
    have yOne : y ≤ 1 := by
      have : (1 : ℝ) / 2 ^ 89 ≤ 1 / 2 := by norm_num
      linarith
    have yCube : y ^ 3 ≤ y := by
      have : y ^ 2 ≤ 1 := pow_le_one₀ y0 yOne
      nlinarith
    have xSq : 2 * x ^ 2 ≤ 7 / 8 * x := by nlinarith
    have cross : 2 * (x + 1 / 2 ^ 89) ^ 2 ≤ 2 * x ^ 2 + 4 / 2 ^ 89 * x + 2 / 2 ^ 89 * (2 ^ 31 * x) := by
      have dd : (1 : ℝ) / 2 ^ 89 * (1 / 2 ^ 89) ≤ 1 / 2 ^ 89 * (2 ^ 31 * x) :=
        mul_le_mul_of_nonneg_left dSmall (by positivity)
      nlinarith
    have cubeTerm : y ^ 3 / 2 ^ 117 ≤ (x + 2 ^ 31 * x) / 2 ^ 117 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have total : 2 * x ^ 2 + 4 / 2 ^ 89 * x + 2 / 2 ^ 89 * (2 ^ 31 * x) + (x + 2 ^ 31 * x) / 2 ^ 117 ≤
        255 / 256 * x := by
      have coeff : (7 : ℝ) / 8 + 4 / 2 ^ 89 + 2 / 2 ^ 89 * 2 ^ 31 + (1 + 2 ^ 31) / 2 ^ 117 ≤ 255 / 256 := by
        norm_num
      have scaled := mul_le_mul_of_nonneg_right coeff x0
      nlinarith
    nlinarith
  · -- upper range: s ≤ 2x^2 + 2^-20, then nine intervals
    have yTwo : y ≤ 2 := by
      have : (1 : ℝ) / 2 ^ 89 ≤ 1 := by norm_num
      linarith
    have upperExp : s ≤ 2 * x ^ 2 + 1 / 2 ^ 20 := by
      have cubeTerm : y ^ 3 / 2 ^ 117 ≤ 8 / 2 ^ 117 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := pow_le_pow_left₀ y0 yTwo 3
        norm_num at this
        linarith
      have cross : 2 * (x + 1 / 2 ^ 89) ^ 2 ≤ 2 * x ^ 2 + 4 / 2 ^ 89 + 2 / 2 ^ 178 := by
        have : 4 / 2 ^ 89 * x ≤ 4 / 2 ^ 89 := by
          have := mul_le_mul_of_nonneg_left xTop (by positivity : (0 : ℝ) ≤ 4 / 2 ^ 89)
          linarith
        nlinarith
      have slack : (4 : ℝ) / 2 ^ 89 + 2 / 2 ^ 178 + 8 / 2 ^ 117 ≤ 1 / 2 ^ 20 := by norm_num
      nlinarith
    rcases le_or_gt x (33 / 64) with h1 | h1
    · exact t238_interval (7 / 16) (33 / 64) x s high.le h1 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (37 / 64) with h2 | h2
    · exact t238_interval (33 / 64) (37 / 64) x s h1.le h2 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (41 / 64) with h3 | h3
    · exact t238_interval (37 / 64) (41 / 64) x s h2.le h3 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (11 / 16) with h4 | h4
    · exact t238_interval (41 / 64) (11 / 16) x s h3.le h4 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (47 / 64) with h5 | h5
    · exact t238_interval (11 / 16) (47 / 64) x s h4.le h5 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (25 / 32) with h6 | h6
    · exact t238_interval (47 / 64) (25 / 32) x s h5.le h6 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (27 / 32) with h7 | h7
    · exact t238_interval (25 / 32) (27 / 32) x s h6.le h7 x0 upperExp (by norm_num) (by norm_num)
    rcases le_or_gt x (59 / 64) with h8 | h8
    · exact t238_interval (27 / 32) (59 / 64) x s h7.le h8 x0 upperExp (by norm_num) (by norm_num)
    · exact t238_interval (59 / 64) 1 x s h8.le xTop x0 upperExp (by norm_num) (by norm_num)

/-- The tree term at 238 bits fits `255·q/2^128` of the `q/2^120` binding budget. -/
theorem t238_tree_budget (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q + 2^31) :
    ENNReal.ofReal (1 - Real.exp (-((calls : ℝ) * ((calls : ℝ) - 1) / 2 ^ 239 + (calls : ℝ) ^ 3 / (3 * 4 ^ 238)))) ≤
      255 * (q : ENNReal) / 2^128 := by
  refine (ENNReal.ofReal_le_ofReal (t238_tree_real q calls positive small replayed)).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

end CommitGolfCandidate
