import CommitGolfCandidate.JointOracleBudget

/-! Arithmetic for a shared 238-bit survival envelope with one initial virtual slot
and the private replay allowance. This module does not establish the oracle bridge. -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192

theorem joint_margin_242 (q calls : Nat) (positive : 1 ≤ q) (small : q < 2^120)
    (replay : calls ≤ q+2^31) :
    1-Real.exp (-collisionExponent (2^238) (calls+1)) ≤ (q : ℝ)/2^120 := by
  by_cases tiny : q < 959
  · have mSmall : calls+1 ≤ 2^32 := by omega
    have mr : ((calls+1 : Nat) : ℝ) ≤ 2^32 := by exact_mod_cast mSmall
    have m0 : (0 : ℝ) ≤ (calls+1 : Nat) := by positivity
    have square : ((calls+1 : Nat) : ℝ)^2 ≤ (2^32 : ℝ)^2 := by
      nlinarith
    have gap : (0 : ℝ) < 2^238-((calls+1 : Nat) : ℝ) := by
      have : (2 : ℝ)^32 < 2^238 := by norm_num
      linarith
    have exponent : collisionExponent (2^238) (calls+1) ≤ (1 : ℝ)/2^120 := by
      unfold collisionExponent
      rw [div_div]
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
        (by simpa only [Nat.cast_add,Nat.cast_one] using gap))).2
      push_cast at mr m0 square
      nlinarith
    have linear : 1-Real.exp (-collisionExponent (2^238) (calls+1)) ≤
        collisionExponent (2^238) (calls+1) := by
      linarith [Real.add_one_le_exp (-collisionExponent (2^238) (calls+1))]
    have q1 : (1 : ℝ) ≤ q := by exact_mod_cast positive
    exact linear.trans (exponent.trans (div_le_div_of_nonneg_right q1 (by positivity)))
  · have nextPositive : 1 ≤ q+1 := by omega
    have nextSmall : q+1 ≤ 2^120 := by omega
    have nextReplay : calls+1 ≤ q+1+2^31 := by omega
    have bound := internal_margin_243 (q+1) (calls+1) nextPositive nextSmall nextReplay
    have qLower : (959 : ℝ) ≤ q := by exact_mod_cast (show 959 ≤ q by omega)
    push_cast at bound
    nlinarith

theorem joint_margin_242_capped (q calls : Nat) (positive : 1 ≤ q)
    (replay : calls ≤ q+2^31) :
    min 1 (1-Real.exp (-collisionExponent (2^238) (calls+1))) ≤ (q : ℝ)/2^120 := by
  by_cases small : q < 2^120
  · exact (min_le_right _ _).trans (joint_margin_242 q calls positive small replay)
  · have large : (2^120 : ℝ) ≤ q := by exact_mod_cast (show 2^120 ≤ q by omega)
    exact (min_le_left _ _).trans ((le_div_iff₀ (by positivity)).2 (by simpa using large))

end TwoPermutationPrototype.Sampling
