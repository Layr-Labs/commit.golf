import CommitGolfCandidate.HidingCoordinate

/-! Compose the single-unopened-coordinate bound across the complete message.
Coordinates opened by the verifier are equal in both messages and cost nothing.
The fixed-cache result will be averaged over the adaptive first stage. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleComp.DeferredSampling

def hybridMessage (left right : Message) (indices : List Index) : Message :=
  fun index => if index ∈ indices then right index else left index

theorem hybrid_message_nil (left right : Message) : hybridMessage left right [] = left := by
  funext index
  simp [hybridMessage]

theorem hybrid_message_cons (left right : Message) (index : Index) (indices : List Index) :
    hybridMessage left right (index :: indices) =
      Function.update (hybridMessage left right indices) index (right index) := by
  funext requested
  by_cases same : requested = index
  · subst requested
    simp [hybridMessage]
  · simp [hybridMessage, same]

attribute [local irreducible] heapQueryBudget

theorem reference_observation_hybrid {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec 512))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (indices : List Index) :
    tvDist (referenceObservation permutation cache left positions observe)
      (referenceObservation permutation cache (hybridMessage left right indices) positions observe) ≤
      (indices.length : ℝ) *
        (16 * ((keys.card + ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256) := by
  let loss : ℝ := 16 * ((keys.card + ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256
  have nonnegative : 0 ≤ loss := by positivity
  change _ ≤ (indices.length : ℝ)*loss
  induction indices with
  | nil => simp only [hybrid_message_nil, tvDist_self, List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons index indices ih =>
    have step : tvDist
        (referenceObservation permutation cache (hybridMessage left right indices) positions observe)
        (referenceObservation permutation cache (hybridMessage left right (index :: indices)) positions observe) ≤ loss := by
      rw [hybrid_message_cons]
      by_cases opened : index ∈ positions
      · have same : right index = hybridMessage left right indices index := by
          unfold hybridMessage
          split
          · rfl
          · exact (agree index opened).symm
        rw [same, Function.update_eq_self, tvDist_self]
        exact nonnegative
      · have changed := reference_observation_coordinate_distance permutation cache keys covered
          (hybridMessage left right indices) positions observe budget bounded index opened
          (hybridMessage left right indices index) (right index)
        simpa only [Function.update_eq_self] using changed
    refine ((tvDist_triangle _ _ _).trans (add_le_add ih step)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)

/-- Full statistical hiding for two fixed messages agreeing on the opened set,
conditional on any finite cache of earlier oracle answers. -/
theorem reference_observation_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec 512))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Message) (positions : Positions)
    (agree : ∀ index ∈ positions, left index = right index)
    (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget) :
    tvDist (referenceObservation permutation cache left positions observe)
      (referenceObservation permutation cache right positions observe) ≤
      (LENGTH : ℝ) *
        (16 * ((keys.card + ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256) := by
  have all : hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext index
    simp [hybridMessage]
  have result := reference_observation_hybrid permutation cache keys covered left right positions agree
    observe budget bounded (Finset.univ.toList : List Index)
  simpa only [all, Finset.length_toList, Finset.card_univ, Index, Fintype.card_fin] using result

end CommitGolfCandidate
