import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingDistribution

/-! Fresh-salt bounds before commitment. These apply to any query transcript
fixed by the first adversary stage. Queries after receiving the commitment and
opening still require the separate adaptive hiding argument. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingFreshnessDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- Every coordinate of a uniform finite function is uniform. Keeping the domain
and range abstract avoids expanding the concrete challenge's huge sample space. -/
theorem uniform_coordinate_distribution {Domain Range : Type}
    [Finite Domain] [DecidableEq Domain] [Finite Range] [Nonempty Range]
    [SampleableType Range] [SampleableType (Domain → Range)] (index : Domain) :
    𝒟[(fun salt : Domain → Range => salt index) <$> ($ᵗ (Domain → Range))] =
      𝒟[$ᵗ Range] := by
  classical
  have marginal := evalDist_uniformSample_bind_update_map
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index
    (fun salt : Domain → Range => salt index)
  simp only [Function.update_self] at marginal
  rw [bind_pure_comp] at marginal
  calc
    _ = 𝒟[do let value ← $ᵗ Range
             let _ ← $ᵗ (Domain → Range)
             pure value] := marginal.symm
    _ = 𝒟[($ᵗ Range) >>= fun value => pure value] := by
      apply _root_.evalDist_bind_congr
      intro value
      exact OracleComp.evalDist_bind_const _ _
    _ = _ := by rw [bind_pure]

private theorem uniform_coordinate_probability {Domain Range : Type}
    [Finite Domain] [DecidableEq Domain] [Fintype Range] [Nonempty Range]
    [SampleableType Range] [SampleableType (Domain → Range)] (index : Domain) (guess : Range) :
    (prEvent ((fun salt : Domain → Range => salt index = guess) <$> (($ᵗ (Domain → Range))))) =
      (Fintype.card Range : ENNReal)⁻¹ := by
  have same := (EvalDistEq.of_evalDist_eq (uniform_coordinate_distribution index)).prEvent_eq
    (fun value => value = guess)
  simpa only [prEvent_map, SampleableType.prEvent_uniformSample_eq_singleton] using same

theorem uniform_bitvector_guess (count width : Nat) (index : Fin count)
    (guess : BitVec width) :
    (prEvent ((fun salt : Fin count → BitVec width => salt index = guess) <$> (($ᵗ (Fin count → BitVec width))))) =
      1 / (2^width : ENNReal) := by
  rw [uniform_coordinate_probability]
  have cardinal : Fintype.card (BitVec width) = 2^width := by simp
  rw [cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat, one_div]

/-- A fixed 128-bit guess hits one newly sampled 128-bit salt with probability exactly `2^-128`. -/
theorem salt128_guess_probability (index : Index) (guess : Salt) :
    (prEvent ((fun salt : Index → Salt => salt index = guess) <$> (($ᵗ (Index → Salt))))) =
      1 / (2^128 : ENNReal) :=
  uniform_bitvector_guess LENGTH 128 index guess

/-- A fixed guess hits one newly sampled salt with probability exactly 2^-256. -/
theorem salt_guess_probability (index : Index) (guess : Digest) :
    (prEvent ((fun salt : Index → Digest => salt index = guess) <$> (($ᵗ (Index → Digest))))) =
      1 / (2^256 : ENNReal) :=
  uniform_bitvector_guess LENGTH 256 index guess

/-- Union bound for any finite set of preselected position/salt guesses. -/
theorem fresh_salt_guesses_bound (guesses : Finset (Index × Digest)) :
    (prEvent ((fun salt : Index → Digest => ∃ guess ∈ guesses, salt guess.1 = guess.2) <$> (($ᵗ (Index → Digest))))) ≤ (guesses.card : ENNReal) / 2^256 := by
  refine (prEvent_exists_finset_le guesses ($ᵗ (Index → Digest))
    (fun guess salt => salt guess.1 = guess.2)).trans ?_
  simp only [salt_guess_probability, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
  exact le_rfl

/-- A first-stage compression input can hit the first leaf-hash input only if
its low 256 bits guess that leaf's fresh salt. Ignoring the message block gives
a bound valid even when the adversary chose the message after its queries. -/
theorem prior_compression_salt_bound (queries : Finset (BitVec COMPRESSION_INPUT_LENGTH)) :
    (prEvent ((fun salt : Index → Digest =>
      ∃ index : Index, ∃ input ∈ queries, salt index = input.extractLsb' 0 256) <$> (($ᵗ (Index → Digest))))) ≤
      (LENGTH : ENNReal) * (queries.card : ENNReal) / 2^256 := by
  classical
  let guesses := (Finset.univ : Finset Index) ×ˢ queries
  have union := prEvent_exists_finset_le guesses ($ᵗ (Index → Digest))
    (fun guess salt => salt guess.1 = guess.2.extractLsb' 0 256)
  have event : (fun salt : Index → Digest =>
      ∃ guess ∈ guesses, salt guess.1 = guess.2.extractLsb' 0 256) =
      (fun salt => ∃ index : Index, ∃ input ∈ queries, salt index = input.extractLsb' 0 256) := by
    funext salt
    simp only [guesses, Finset.mem_product, Finset.mem_univ, true_and, Prod.exists]
  rw [event] at union
  refine union.trans ?_
  simp only [salt_guess_probability, Finset.sum_const, nsmul_eq_mul, guesses,
    Finset.card_product, Finset.card_univ, Index, Fintype.card_fin, Nat.cast_mul,
    div_eq_mul_inv, one_mul]
  exact le_rfl

/-- The same bound survives an arbitrary randomized first stage. Its queries
and messages may depend on its earlier oracle replies; only the later salt draw
must be fresh. This does not assume a fixed, nonadaptive first-stage transcript. -/
theorem prior_stage_salt_bound {State : Type} (before : ProbComp State)
    (queries : State → Finset (BitVec COMPRESSION_INPUT_LENGTH)) (queryBudget : Nat)
    (bounded : ∀ state ∈ support before, (queries state).card ≤ queryBudget) :
    (prEvent ((fun result : State × (Index → Digest) =>
      ∃ index : Index, ∃ input ∈ queries result.1,
        result.2 index = input.extractLsb' 0 256) <$> ((do
          let state ← before
          let salt ← $ᵗ (Index → Digest)
          pure (state, salt))))) ≤
      (LENGTH : ENNReal) * (queryBudget : ENNReal) / 2^256 := by
  apply prEvent_bind_le_of_forall_le_of_support
  intro state reached
  rw [bind_pure_comp, prEvent_map]
  refine (prior_compression_salt_bound (queries state)).trans ?_
  apply ENNReal.div_le_div_right
  gcongr
  exact bounded state reached

end CommitGolfCandidate
