import CommitGolfCandidate.HidingGameIntegration
import CommitGolfCandidate.HidingTaggedSalt

/-! Statistical hiding of the submitted machine-derived scheme. The proof covers
the complete two-stage oracle-adaptive game and every opening size, including zero.
Every unopened leaf's Call 0 input carries a unique 64-bit position tag alongside
a 128-bit uniform salt, leaving ample margin below the fixed 120-bit requirement. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingSecurityDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

attribute [local irreducible] heapQueryBudget

/-- Combined tagged-salt reprogramming loss plus hybrid leaf-replacement loss stays
well below the challenge's 120-bit hiding target. -/
theorem hiding_loss_le_target (positions : Positions) (known budget : Nat) (knownBound : known ≤ budget) :
    2 * (((3 * budget : Nat) : ℝ) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ℝ) / 2 ^ 192) +
    (LENGTH : ℝ) *
      (16 * ((known + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2 ^ 256) ≤
      ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  have treeFormula := heap_query_budget_formula 8 LOG_LENGTH
  have treeBound : heapQueryBudget 8 LOG_LENGTH ≤ 9 * LENGTH := by
    change heapQueryBudget 8 LOG_LENGTH + 1 = 9 * LENGTH at treeFormula
    omega
  have total : known + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 ≤
      budget + ((1 + 784 * LENGTH) * (9 * LENGTH) + budget) + 8 := by
    gcongr
  calc
    _ ≤ 2 * (((3 * budget : Nat) : ℝ) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ℝ) / 2 ^ 192) +
        (LENGTH : ℝ) *
          (16 * ((budget + ((1 + 784 * LENGTH) * (9 * LENGTH) + budget) + 8 : Nat) : ℝ) / 2 ^ 256) := by
      gcongr
    _ ≤ _ := by
      norm_num [LENGTH, LOG_LENGTH, HIDING_SECURITY_BITS, Nat.cast_add, Nat.cast_mul]
      nlinarith [Nat.cast_nonneg (α := ℝ) budget]

/-- Conditional on each reachable first-stage transcript, combine the two tagged-salt
reprogramming hops (`Real(m₀) ↔ Hybrid(m₀)` and `Hybrid(m₁) ↔ Real(m₁)`) with the
coordinatewise hybrid hiding bound (`Hybrid(m₀) ↔ Hybrid(m₁)`). -/
theorem staged_hiding_distance {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (stagedHiding permutation adversary false) (stagedHiding permutation adversary true) ≤
      ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  unfold stagedHiding
  rw [bind_eq_attach_bind (compressionRun permutation adversary.choose ∅)]
  rw [bind_eq_attach_bind (compressionRun permutation adversary.choose ∅)]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  rintro ⟨result, reached⟩
  obtain ⟨keys, size, covered⟩ := first_stage_cache_bound permutation adversary.choose budget
    (hiding_choose_query_bound adversary bounded) result reached
  have agree : ∀ index ∈ result.1.positions, result.1.message₀ index = result.1.message₁ index := by
    intro index member
    exact congrFun result.1.agree ⟨index, member⟩
  have obsBound := staged_observe_query_bound permutation adversary bounded result reached
  have hop0 := reference_vs_hybrid_distance permutation result.2 keys covered budget size
    result.1.message₀ result.1.positions (adversary.observe result.1.aux) obsBound
  have hopMid := hybrid_observation_distance permutation result.2 keys covered
    result.1.message₀ result.1.message₁ result.1.positions agree
    (adversary.observe result.1.aux) budget obsBound
  have hop1 := reference_vs_hybrid_distance permutation result.2 keys covered budget size
    result.1.message₁ result.1.positions (adversary.observe result.1.aux) obsBound
  rw [measureTVDist_comm] at hop1
  have tri1 := (measureTVDist_triangle
    (referenceObservation permutation result.2 result.1.message₀ result.1.positions (adversary.observe result.1.aux))
    (hybridObservation permutation result.2 result.1.message₀ result.1.positions (adversary.observe result.1.aux))
    (hybridObservation permutation result.2 result.1.message₁ result.1.positions (adversary.observe result.1.aux))).trans
    (add_le_add hop0 hopMid)
  have tri2 := (measureTVDist_triangle
    (referenceObservation permutation result.2 result.1.message₀ result.1.positions (adversary.observe result.1.aux))
    (hybridObservation permutation result.2 result.1.message₁ result.1.positions (adversary.observe result.1.aux))
    (referenceObservation permutation result.2 result.1.message₁ result.1.positions (adversary.observe result.1.aux))).trans
    (add_le_add tri1 hop1)
  have combined : measureTVDist
      (referenceObservation permutation result.2 result.1.message₀ result.1.positions (adversary.observe result.1.aux))
      (referenceObservation permutation result.2 result.1.message₁ result.1.positions (adversary.observe result.1.aux)) ≤
      2 * (((3 * budget : Nat) : ℝ) / 2 ^ 128 + (6 * (LENGTH * LENGTH) : ℝ) / 2 ^ 192) +
      (LENGTH : ℝ) *
        (16 * ((keys.card + ((1 + 784 * result.1.positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2 ^ 256) := by
    linarith
  exact combined.trans (hiding_loss_le_target result.1.positions keys.card budget size)

/-- Hiding for the actual RISC-V commitment and opening images, at the contract's
error function. No separate simulator, efficiency axiom, or abstract scheme is assumed. -/
theorem submission_hiding : submission.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro openingSize budget
    unfold HIDING_ERROR
    apply le_min (by norm_num)
    positivity
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _) ?_
    have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm)
      (fun permutation => stagedHiding permutation adversary false)
      (fun permutation => stagedHiding permutation adversary true) (by positivity)
      (fun permutation => staged_hiding_distance permutation adversary bounded)
    simpa only [measureTVDist, hiding_staged_distribution] using distance

end CommitGolfCandidate
