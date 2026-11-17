import CommitGolfCandidate.HidingCoordinate

/-! Compose the single-coordinate bound across the complete message. Each hybrid
is a whole game (first stage inside), so the adaptive choice of messages and
positions needs no conditioning. Coordinates the first stage opens are equal in
both messages; the per-leaf statement covers them at no extra cost. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingHybridDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
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

variable {State Output : Type} {openingSize : Nat}

theorem hybrid_game_step
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (index : Index) (indices : List Index) :
    measureTVDist
      (hidingGame adversary fun challenge =>
        hybridMessage challenge.message₀ challenge.message₁ indices)
      (hidingGame adversary fun challenge =>
        hybridMessage challenge.message₀ challenge.message₁ (index :: indices)) ≤
      4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192 := by
  have step := hiding_coordinate_distance adversary budget chooseBound observeBound
    (fun challenge => hybridMessage challenge.message₀ challenge.message₁ indices) index
    (fun challenge => hybridMessage challenge.message₀ challenge.message₁ indices index)
    (fun challenge => challenge.message₁ index)
    (fun _ _ => rfl)
    (fun challenge opened => by
      show challenge.message₁ index =
        if index ∈ indices then challenge.message₁ index else challenge.message₀ index
      split
      · rfl
      · exact (congrFun challenge.agree ⟨index, opened⟩).symm)
  have left : (fun challenge : Hiding.HidingChallenge State openingSize =>
      hybridMessage challenge.message₀ challenge.message₁ indices) =
      fun challenge => Function.update (hybridMessage challenge.message₀ challenge.message₁ indices)
        index (hybridMessage challenge.message₀ challenge.message₁ indices index) := by
    funext challenge
    rw [Function.update_eq_self]
  have right : (fun challenge : Hiding.HidingChallenge State openingSize =>
      hybridMessage challenge.message₀ challenge.message₁ (index :: indices)) =
      fun challenge => Function.update (hybridMessage challenge.message₀ challenge.message₁ indices)
        index (challenge.message₁ index) := by
    funext challenge
    rw [hybrid_message_cons]
  rw [right, left]
  exact step

theorem hybrid_game_distance
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (indices : List Index) :
    measureTVDist
      (hidingGame adversary fun challenge =>
        hybridMessage challenge.message₀ challenge.message₁ [])
      (hidingGame adversary fun challenge =>
        hybridMessage challenge.message₀ challenge.message₁ indices) ≤
      (indices.length : ℝ) *
        (4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192) := by
  let loss : ℝ := 4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192
  change _ ≤ (indices.length : ℝ)*loss
  induction indices with
  | nil => simp only [measureTVDist_self, List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons index indices ih =>
    have step : measureTVDist
        (hidingGame adversary fun challenge =>
          hybridMessage challenge.message₀ challenge.message₁ indices)
        (hidingGame adversary fun challenge =>
          hybridMessage challenge.message₀ challenge.message₁ (index :: indices)) ≤ loss :=
      hybrid_game_step adversary budget chooseBound observeBound index indices
    refine ((measureTVDist_triangle _ _ _).trans (add_le_add ih step)).trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    exact le_of_eq (by ring)

/-- Statistical hiding of the reference game for an adversary whose two stages
are each structurally bounded: all `LENGTH` coordinates are replaced in turn. -/
theorem hiding_game_distance
    (adversary : Hiding.HidingAdversary State Output openingSize) (budget : Nat)
    (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget) :
    measureTVDist (hidingGame adversary fun challenge => challenge.message₀)
      (hidingGame adversary fun challenge => challenge.message₁) ≤
      (LENGTH : ℝ) *
        (4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192) := by
  have all (left right : Message) :
      hybridMessage left right (Finset.univ.toList : List Index) = right := by
    funext index
    simp [hybridMessage]
  have result := hybrid_game_distance adversary budget chooseBound observeBound
    (Finset.univ.toList : List Index)
  simpa only [all, hybrid_message_nil, Finset.length_toList, Finset.card_univ, Index,
    Fintype.card_fin] using result

end CommitGolfCandidate
