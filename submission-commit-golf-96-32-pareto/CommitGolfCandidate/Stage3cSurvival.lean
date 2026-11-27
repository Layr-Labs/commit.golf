import CommitGolf.Oracle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
namespace CommitGolfCandidate
open scoped BigOperators
noncomputable section
variable (w : Nat)
def lowBits (v : BitVec 256) : BitVec w := v.extractLsb' 0 w
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


end
end CommitGolfCandidate
