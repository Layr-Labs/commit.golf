import Mathlib.Tactic

/-! The exact pinned-leaf event bound for 240-bit leaf digests fits in `9q/2^124`. -/
namespace TwoPermutationPrototype.Sampling

set_option exponentiation.threshold 2048
set_option maxHeartbeats 1000000

theorem pinned_peer_collision_margin (q queries : ℕ) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (count : queries ≤ q + 2^31 + 4) :
    (((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^1360 + 2^897) + (queries : ℝ)*2^896) /
      (2^1600 - (queries : ℝ)) ≤ 9*(q : ℝ)/2^124 := by
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qUpper : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have nonneg : (0 : ℝ) ≤ queries := by positivity
  have terms : (queries : ℝ) ≤ (q : ℝ) + 2^31 + 4 := by exact_mod_cast count
  have queriesUpper : (queries : ℝ) ≤ 2^121 := by
    have threshold : (2 : ℝ)^120 + 2^31 + 4 ≤ 2^121 := by norm_num
    linarith
  have denominator : (2 : ℝ)^1600 - 2^121 ≤ 2^1600-(queries : ℝ) := by linarith
  have denominatorPos : (0 : ℝ) < 2^1600-(queries : ℝ) := by
    have : (0 : ℝ) < 2^1600 - 2^121 := by norm_num
    linarith
  have squareBound : (queries : ℝ)^2 ≤ (q : ℝ)*(2^120 + 2^65) := by
    let extra : ℝ := 2^31+4
    have leSum : (queries : ℝ) ≤ q + extra := by linarith [show extra = (2:ℝ)^31+4 from rfl]
    have sq := mul_le_mul leSum leSum nonneg (by positivity)
    have qsq := mul_le_mul_of_nonneg_right qUpper qNonneg
    have esq : 2*extra*q + extra^2 ≤ q*2^65 := by
      have e1 : 2*extra ≤ 2^33 := by norm_num [extra]
      have e2 : extra^2 ≤ 2^64 := by norm_num [extra]
      nlinarith
    nlinarith
  have linearBound : (queries : ℝ) ≤ (q : ℝ)*2^33 := by
    have extra : (2 : ℝ)^31 + 4 ≤ 2^32 := by norm_num
    nlinarith
  have pairs : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^1360 + 2^897) ≤
      (queries : ℝ)^2 / 2 * (2^1360 + 2^897) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have : (queries : ℝ) * ((queries : ℝ) - 1) ≤ (queries : ℝ)^2 := by nlinarith
    linarith
  have total : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^1360 + 2^897) + (queries : ℝ)*2^896 ≤
      (q : ℝ) * ((2^120 + 2^65) * (2^1360 + 2^897) / 2 + 2^929) := by
    have a := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ (2^1360 + 2^897)/2)
    have b := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^896)
    nlinarith
  have constant : (2^120 + 2^65 : ℝ) * (2^1360 + 2^897) / 2 + 2^929 ≤ 9 / 2^124 * (2^1600 - 2^121) := by
    norm_num
  rw [div_le_iff₀ denominatorPos]
  have scaled := mul_le_mul_of_nonneg_left constant qNonneg
  have den := mul_le_mul_of_nonneg_left denominator (by positivity : (0 : ℝ) ≤ 9*(q : ℝ)/2^124)
  have eq : (q : ℝ) * (9 / 2^124 * (2^1600 - 2^121)) = 9*(q : ℝ)/2^124 * (2^1600 - 2^121) := by ring
  linarith

end TwoPermutationPrototype.Sampling
