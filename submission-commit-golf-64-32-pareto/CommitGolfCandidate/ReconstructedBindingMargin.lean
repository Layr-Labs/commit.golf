import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

namespace CommitGolfCandidate.Reconstruction.Binding

private theorem power_tangent (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) (n : Nat) :
    (n+1 : ℕ) * r^n * (x-r) ≤ x^(n+1) - r^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have mono : 0 ≤ (x^(n+1)-r^(n+1))*(x-r) := by
      rcases le_total x r with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (pow_le_pow_left₀ hx h _)) (sub_nonpos.mpr h)
      · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hr h _)) (sub_nonneg.mpr h)
    have scaled := mul_le_mul_of_nonneg_left ih hr
    push_cast at scaled ⊢
    rw [pow_succ x (n+1), pow_succ r (n+1)]
    rw [pow_succ r n] at mono scaled ⊢
    nlinarith only [scaled, mono]

/-- The first sixteen terms of -log(1-x) lie above 2.45 x² on the entire
unit interval. The tangent bounds for powers after division by x² reduce
the final check to rational arithmetic. -/
private theorem log_polynomial (x : ℝ) (hx : 0 ≤ x) (small : x ≤ 1) :
    (245/100)*x^2 ≤ ∑ i ∈ Finset.range 16, x^(i+1)/((i:ℝ)+1) := by
  let r : ℝ := 717/1000
  have main : ∀ n : Nat, ((n+1 : ℕ) : ℝ)*r^n*(x-r)*x^2 + r^(n+1)*x^2 ≤ x^(n+3) := by
    intro n
    have t := mul_le_mul_of_nonneg_right (power_tangent x r hx (by norm_num [r]) n) (sq_nonneg x)
    calc _ ≤ (x^(n+1)-r^(n+1))*x^2 + r^(n+1)*x^2 := by linarith
         _ = _ := by ring
  have one := mul_nonneg hx (sq_nonneg (x-r))
  have cube := mul_le_mul_of_nonneg_right small (sq_nonneg x)
  rw [show x*x^2 = x^3 by ring, one_mul] at cube
  have two := sq_nonneg x
  have t0 := main 0
  have t1 := main 1
  have t2 := main 2
  have t3 := main 3
  have t4 := main 4
  have t5 := main 5
  have t6 := main 6
  have t7 := main 7
  have t8 := main 8
  have t9 := main 9
  have t10 := main 10
  have t11 := main 11
  have t12 := main 12
  have t13 := main 13
  norm_num [r, Finset.sum_range_succ] at one t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ⊢
  linarith only [one, cube, two, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13]

/-- Nonlinear birthday comparison needed by this profile's largest paid
projection fibers. This holds uniformly, including near the maximum ratio. -/
theorem weighted_survival_margin (x : ℝ) (hx : 0 ≤ x) (small : x ≤ 1) :
    1 - Real.exp (-(245/100)*x^2) ≤ x := by
  by_cases endpt : x = 1
  · rw [endpt]; linarith [Real.exp_pos (-(245/100)*(1:ℝ)^2)]
  have lt : x < 1 := lt_of_le_of_ne small endpt
  have series := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by simpa [abs_of_nonneg hx] using lt)
  have sub := series.summable.sum_le_tsum (Finset.range 16) (fun i _ => by positivity)
  rw [series.tsum_eq] at sub
  have total := (log_polynomial x hx small).trans sub
  have le : Real.log (1-x) ≤ -(245/100)*x^2 := by linarith
  have e := Real.exp_le_exp.mpr le
  rw [Real.exp_log (by linarith)] at e
  linarith

end CommitGolfCandidate.Reconstruction.Binding
