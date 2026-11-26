import CommitGolfCandidate.HidingHybrid

import CommitGolfCandidate.TruncHidingCoordinate

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleComp.DeferredSampling

local instance hidingHybridDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000

set_option maxHeartbeats 800000

attribute [local irreducible] heapQueryBudget

theorem hybrid_observation_list {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (indices : List Index) :
    measureTVDist (hybridObservation permutation cache left positions observe)
      (hybridObservation permutation cache (hybridMessage left right indices) positions observe) ≤
      (indices.length : ℝ) *
        (16 * ((keys.card + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256) := by
  let loss : ℝ := 16 * ((keys.card + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256
  have nonnegative : 0 ≤ loss := by positivity
  change _ ≤ (indices.length : ℝ) * loss
  induction indices with
  | nil => simp only [hybrid_message_nil, measureTVDist_self, List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons index indices ih =>
    have step : measureTVDist
        (hybridObservation permutation cache (hybridMessage left right indices) positions observe)
        (hybridObservation permutation cache (hybridMessage left right (index :: indices)) positions observe) ≤ loss := by
      rw [hybrid_message_cons]
      by_cases opened : index ∈ positions
      · have same : right index = hybridMessage left right indices index := by
          unfold hybridMessage
          split
          · rfl
          · exact (agree index opened).symm
        rw [same, Function.update_eq_self, measureTVDist_self]
        exact nonnegative
      · have changed := hybrid_observation_coordinate_distance permutation cache keys covered
          (hybridMessage left right indices) positions observe budget bounded index opened
          (hybridMessage left right indices index) (right index)
        simpa only [Function.update_eq_self] using changed
    refine ((measureTVDist_triangle _ _ _).trans (add_le_add ih step)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)

theorem hybrid_observation_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    measureTVDist (hybridObservation permutation cache left positions observe)
      (hybridObservation permutation cache right positions observe) ≤
      (LENGTH : ℝ) *
        (16 * ((keys.card + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256) := by
  have all : hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext index
    simp [hybridMessage]
  have result := hybrid_observation_list permutation cache keys covered left right positions agree
    observe budget bounded (Finset.univ.toList : List Index)
  simpa only [all, Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using result

end CommitGolfCandidate.Trunc
