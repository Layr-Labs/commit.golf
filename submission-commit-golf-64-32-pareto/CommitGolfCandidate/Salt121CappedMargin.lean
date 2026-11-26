import CommitGolfCandidate.NonceChainLayout

namespace TwoPermutationPrototype.Sampling
open CommitGolf
set_option exponentiation.threshold 2048

noncomputable def salt121CappedCharge (t : Nat) : ℝ :=
  min (2*(t : ℝ)) ((t : ℝ)+3*LENGTH) / 2^121 +
    (8*LENGTH*(t : ℝ)+18*LENGTH^2)/2^1343 +
    2*(1525249 : ℝ)*(4*(t : ℝ)+4*LENGTH+1525249)/2^192

theorem salt121_capped_margin (t : Nat) :
    salt121CappedCharge t ≤
      (99999999/100000000 : ℝ)*(((t : ℝ)+1)/2^120) := by
  have nn : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  unfold salt121CappedCharge
  by_cases small : t ≤ 3*LENGTH
  · have bound : (t : ℝ) ≤ 50331648 := by
      exact_mod_cast (show t ≤ 50331648 from small)
    norm_num [LENGTH, LOG_LENGTH]
    rw [min_eq_left (by linarith : 2*(t : ℝ) ≤ (t : ℝ)+50331648)]
    nlinarith
  · have bound : (50331648 : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge small))
    norm_num [LENGTH, LOG_LENGTH]
    rw [min_eq_right (by linarith : (t : ℝ)+50331648 ≤ 2*(t : ℝ))]
    nlinarith

end TwoPermutationPrototype.Sampling
