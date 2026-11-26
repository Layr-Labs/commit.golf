import CommitGolfCandidate.ChainedSchedule
import CommitGolfCandidate.ProjectedCollisionProduct

/-! Generic work accounting and the scalar finite birthday comparison. -/
namespace CommitGolfCandidate.Chained.Weighted
open scoped BigOperators
variable {ι : Type} [Fintype ι]

def work (rate counts : ι → Nat) : Nat := ∑ k, rate k*counts k

theorem component_work (rate counts : ι → Nat) (k : ι) :
    rate k*counts k ≤ work rate counts := by
  classical
  unfold work
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (rate j*counts j)) (Finset.mem_univ k)

theorem weighted_count (rate counts : ι → Nat) (k : ι) (ceiling limit : Nat)
    (rateBound : rate k ≤ limit) (bounded : work rate counts ≤ ceiling) :
    (rate k)^2*counts k ≤ limit*ceiling := by
  calc
    _ = rate k*(rate k*counts k) := by ring
    _ ≤ limit*(rate k*counts k) := Nat.mul_le_mul_right _ rateBound
    _ ≤ _ := Nat.mul_le_mul_left limit ((component_work rate counts k).trans bounded)

theorem sum_squares (cost : ι → ℝ) (nonnegative : ∀ k, 0 ≤ cost k) :
    (∑ k, (cost k)^2) ≤ (∑ k, cost k)^2 := by
  classical
  have component : ∀ k, cost k ≤ ∑ j, cost j := fun k =>
    Finset.single_le_sum (fun j _ => nonnegative j) (Finset.mem_univ k)
  calc
    _ ≤ ∑ k, cost k*(∑ j, cost j) := Finset.sum_le_sum fun k _ => by
      nlinarith [mul_le_mul_of_nonneg_left (component k) (nonnegative k)]
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem scalar_exponent (N m r gap : ℝ) (nonnegative : 0 ≤ m) (room : m < N)
    (positive : 0 < gap) (scaled : gap ≤ r^2*(N-m)) :
    collisionExponent N m ≤ (r*m)^2/(2*gap) := by
  have denominator : 0 < N-m := by linarith
  unfold collisionExponent
  rw [div_div]
  calc
    _ ≤ m^2/(2*(N-m)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ ≤ _ := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have multiplied := mul_le_mul_of_nonneg_right scaled (sq_nonneg m)
      nlinarith only [multiplied]

theorem exponent_sum (N m r : ι → ℝ) (D ceiling limit : ℝ)
    (counts_nonnegative : ∀ k, 0 ≤ m k) (rates_nonnegative : ∀ k, 0 ≤ r k)
    (rates_bounded : ∀ k, r k ≤ limit) (limit_nonnegative : 0 ≤ limit)
    (dense : ∀ k, D ≤ (r k)^2*N k) (bounded : ∑ k, r k*m k ≤ ceiling)
    (room : 0 < D-limit*ceiling) :
    (∑ k, collisionExponent (N k) (m k)) ≤ ceiling^2/(2*(D-limit*ceiling)) := by
  classical
  have cost_nonnegative : ∀ k, 0 ≤ r k*m k := fun k =>
    mul_nonneg (rates_nonnegative k) (counts_nonnegative k)
  have component : ∀ k, r k*m k ≤ ceiling := fun k =>
    (Finset.single_le_sum (fun j _ => cost_nonnegative j) (Finset.mem_univ k)).trans bounded
  have scaled : ∀ k, D-limit*ceiling ≤ (r k)^2*(N k-m k) := by
    intro k
    have consumed : (r k)^2*m k ≤ limit*ceiling := by
      calc
        _ = r k*(r k*m k) := by ring
        _ ≤ limit*(r k*m k) := mul_le_mul_of_nonneg_right (rates_bounded k) (cost_nonnegative k)
        _ ≤ _ := mul_le_mul_of_nonneg_left (component k) limit_nonnegative
    nlinarith [dense k]
  have member_room : ∀ k, m k < N k := by
    intro k
    by_contra closed
    have nonpositive := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (r k)) (sub_nonpos.mpr (not_lt.mp closed))
    linarith [scaled k]
  have squared : (∑ k, r k*m k)^2 ≤ ceiling^2 := by
    have nonnegative := Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset ι)) => cost_nonnegative k)
    simpa only [pow_two] using mul_self_le_mul_self nonnegative bounded
  calc
    _ ≤ ∑ k, (r k*m k)^2/(2*(D-limit*ceiling)) := Finset.sum_le_sum fun k _ =>
      scalar_exponent (N k) (m k) (r k) _ (counts_nonnegative k) (member_room k) room (scaled k)
    _ = (∑ k, (r k*m k)^2)/(2*(D-limit*ceiling)) := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      ((sum_squares (fun k => r k*m k) cost_nonnegative).trans squared) (by positivity)

noncomputable def potential (width counts : ι → Nat) : ENNReal :=
  ∏ k, survival (width k) 0 (counts k)

theorem potential_ge_exp (width counts : ι → Nat) (room : ∀ k, counts k < 2^(width k)) :
    ENNReal.ofReal (Real.exp (-(∑ k, collisionExponent (2^(width k)) (counts k)))) ≤
      potential width counts := by
  calc
    _ = ∏ k, ENNReal.ofReal (Real.exp (-collisionExponent (2^(width k)) (counts k))) := by
      rw [← Finset.sum_neg_distrib,Real.exp_sum,ENNReal.ofReal_prod_of_nonneg]
      intro k _
      exact (Real.exp_pos _).le
    _ ≤ _ := Finset.prod_le_prod' fun k _ => survival_ge_exp (width k) (counts k) (room k)

theorem finite_envelope (rate width counts : ι → Nat) (ceiling : Nat)
    (rate_bound : ∀ k, rate k ≤ 8) (dense : ∀ k, 2^238 ≤ (rate k)^2*2^(width k))
    (bounded : work rate counts ≤ ceiling) (small : 8*ceiling < 2^238) :
    ENNReal.ofReal (Real.exp (-(ceiling : ℝ)^2/(2*(2^238-8*(ceiling : ℝ))))) ≤
      potential width counts := by
  have real_bound : ∑ k, (rate k : ℝ)*(counts k : ℝ) ≤ (ceiling : ℝ) := by
    unfold work at bounded
    exact_mod_cast bounded
  have real_density : ∀ k, (2 : ℝ)^238 ≤ (rate k : ℝ)^2*2^(width k) := by
    intro k
    exact_mod_cast dense k
  have real_rates : ∀ k, (rate k : ℝ) ≤ 8 := by
    intro k
    exact_mod_cast rate_bound k
  have room : (0 : ℝ) < 2^238-8*(ceiling : ℝ) := by
    have real_small : 8*(ceiling : ℝ) < 2^238 := by exact_mod_cast small
    linarith
  have exponents := exponent_sum (fun k => (2 : ℝ)^(width k)) (fun k => (counts k : ℝ))
    (fun k => (rate k : ℝ)) (2^238) ceiling 8
    (fun _ => by positivity) (fun _ => by positivity) real_rates (by norm_num)
    real_density real_bound room
  have member_room : ∀ k, counts k < 2^(width k) := by
    intro k
    have consumed := weighted_count rate counts k ceiling 8 (rate_bound k) bounded
    by_contra closed
    have expanded := Nat.mul_le_mul_left ((rate k)^2) (not_lt.mp closed)
    have density := dense k
    omega
  have compare := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg exponents))
  simpa only [neg_div] using compare.trans (potential_ge_exp width counts member_room)

end CommitGolfCandidate.Chained.Weighted
