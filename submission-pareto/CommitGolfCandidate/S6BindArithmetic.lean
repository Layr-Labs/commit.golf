import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Arithmetic of the binding sum: the truncated compression term (`q + 2c` queries, replies kept
to 240 bits), the leaf term and the group-node term fit the 120-bit target for every budget
`1 ≤ q ≤ 2^120`. -/
namespace CommitGolfCandidate

/-- The three terms over the common denominator `2^256`. -/
theorem s6_detector_arithmetic (q c : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (ceiling : c ≤ 2 ^ 30) :
    (q + 2 * c) * (q + 2 * c - 1) * 2 ^ 15 + ((q + 2 * 2 ^ 26) ^ 2 + q * 2 ^ 129) +
      ((q + 2 ^ 26) ^ 2 + q * 2 ^ 129) ≤ q * 2 ^ 136 := by
  have pair : (q + 2 * c) * (q + 2 * c - 1) ≤ (q + 2 ^ 31) * (q + 2 ^ 31) := by
    have wide : q + 2 * c ≤ q + 2 ^ 31 := by omega
    calc (q + 2 * c) * (q + 2 * c - 1) ≤ (q + 2 * c) * (q + 2 * c) :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ (q + 2 ^ 31) * (q + 2 ^ 31) := Nat.mul_le_mul wide wide
  have square : q * q ≤ q * 2 ^ 120 := Nat.mul_le_mul_left q small
  generalize (q + 2 * c) * (q + 2 * c - 1) = pairs at pair ⊢
  nlinarith [pair, square, positive]

theorem s6_pow_ne_zero (n : Nat) : (2 : ENNReal) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero

theorem s6_pow_ne_top (n : Nat) : (2 : ENNReal) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top

/-- **Final binding arithmetic.** `c` is the replay ceiling of the cap check; the leaf and the
group replay counts are at most `2^26`. -/
theorem s6_binding_arithmetic (q c : Nat) (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (ceiling : c ≤ 2 ^ 30) :
    (((q + 2 * c) * (q + 2 * c - 1) : Nat) : ENNReal) / (2 * 2 ^ 240) +
      (((q : ENNReal) + 2 * 2 ^ 26) ^ 2 / 2 ^ 256 + (q : ENNReal) / 2 ^ 127) +
      (((q : ENNReal) + 2 ^ 26) ^ 2 / 2 ^ 256 + (q : ENNReal) / 2 ^ 127) ≤ (q : ENNReal) / 2 ^ 120 := by
  obtain ⟨pairs, hpairs⟩ : ∃ pairs, (q + 2 * c) * (q + 2 * c - 1) = pairs := ⟨_, rfl⟩
  have arithmetic : pairs * 2 ^ 15 + ((q + 2 * 2 ^ 26) ^ 2 + q * 2 ^ 129) +
      ((q + 2 ^ 26) ^ 2 + q * 2 ^ 129) ≤ q * 2 ^ 136 := by
    rw [← hpairs]
    exact s6_detector_arithmetic q c positive small ceiling
  have castBound : (pairs : ENNReal) * 2 ^ 15 +
      (((q : ENNReal) + 2 * 2 ^ 26) ^ 2 + (q : ENNReal) * 2 ^ 129) +
      (((q : ENNReal) + 2 ^ 26) ^ 2 + (q : ENNReal) * 2 ^ 129) ≤ (q : ENNReal) * 2 ^ 136 := by
    exact_mod_cast arithmetic
  have first : (pairs : ENNReal) / (2 * 2 ^ 240) = (pairs : ENNReal) * 2 ^ 15 / 2 ^ 256 := by
    rw [show (2 : ENNReal) ^ 256 = 2 * 2 ^ 240 * 2 ^ 15 by ring]
    exact (ENNReal.mul_div_mul_right _ _ (s6_pow_ne_zero 15) (s6_pow_ne_top 15)).symm
  have unary : (q : ENNReal) / 2 ^ 127 = (q : ENNReal) * 2 ^ 129 / 2 ^ 256 := by
    rw [show (2 : ENNReal) ^ 256 = 2 ^ 127 * 2 ^ 129 by rw [← pow_add]]
    exact (ENNReal.mul_div_mul_right _ _ (s6_pow_ne_zero 129) (s6_pow_ne_top 129)).symm
  have target : (q : ENNReal) / 2 ^ 120 = (q : ENNReal) * 2 ^ 136 / 2 ^ 256 := by
    rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
    exact (ENNReal.mul_div_mul_right _ _ (s6_pow_ne_zero 136) (s6_pow_ne_top 136)).symm
  rw [hpairs, first, unary, target]
  simp only [ENNReal.div_add_div_same]
  exact ENNReal.div_le_div_right (le_trans (le_of_eq (by ring)) castBound) _

/-- The group search replays the leaves first (`2^26` queries at most), so its budget is
`q + 2^26`; its term with `extra = 2^26` is covered by the group term of
`s6_binding_arithmetic`. -/
theorem s6_group_term_le (q : Nat) (positive : 1 ≤ q) :
    (((q + 2 ^ 26 : Nat) : ENNReal) + ((2 ^ 26 : Nat) : ENNReal)) ^ 2 / 2 ^ 256 ≤
      ((q : ENNReal) + 2 ^ 26) ^ 2 / 2 ^ 256 + (q : ENNReal) / 2 ^ 127 := by
  have arithmetic : (q + 2 ^ 26 + 2 ^ 26) ^ 2 ≤ (q + 2 ^ 26) ^ 2 + q * 2 ^ 129 := by
    nlinarith [positive]
  have castBound : ((q : ENNReal) + 2 ^ 26 + 2 ^ 26) ^ 2 ≤
      ((q : ENNReal) + 2 ^ 26) ^ 2 + (q : ENNReal) * 2 ^ 129 := by
    exact_mod_cast arithmetic
  have unary : (q : ENNReal) / 2 ^ 127 = (q : ENNReal) * 2 ^ 129 / 2 ^ 256 := by
    rw [show (2 : ENNReal) ^ 256 = 2 ^ 127 * 2 ^ 129 by rw [← pow_add]]
    exact (ENNReal.mul_div_mul_right _ _ (s6_pow_ne_zero 129) (s6_pow_ne_top 129)).symm
  rw [unary, ENNReal.div_add_div_same]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right castBound _

end CommitGolfCandidate
