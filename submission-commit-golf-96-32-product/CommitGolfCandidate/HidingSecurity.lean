import CommitGolfCandidate.HidingGameIntegration

/-! Statistical hiding of the submitted machine-derived scheme. The proof covers
the complete two-stage oracle-adaptive game and every opening size, including zero.
The deliberately loose recomputation bound is below the fixed 120-bit requirement. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingSecurityDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

attribute [local irreducible] heapQueryBudget

/-- Even charging a full tree recomputation for every cap node and every serialized
proof byte (plus the 64 chain calls) leaves ample room
under the challenge's 120-bit target. This is proof-only query accounting. -/
theorem hiding_loss_le_target (positions : Positions) (known budget : Nat) (knownBound : known ≤ budget) :
    (LENGTH : ℝ) *
      (16 * ((known + (transcriptBudget positions.card + budget) + 8 : Nat) : ℝ) / 2^256) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa only [Index, Fintype.card_fin] using Finset.card_le_univ positions
  have treeFormula := heap_query_budget_formula 8 LOG_LENGTH
  have treeBound : heapQueryBudget 8 LOG_LENGTH ≤ 9*LENGTH := by
    change heapQueryBudget 8 LOG_LENGTH+1 = 9*LENGTH at treeFormula
    omega
  have total : known + (transcriptBudget positions.card + budget) + 8 ≤
      budget + ((4224+576*LENGTH)*(9*LENGTH)+64 + budget) + 8 := by
    unfold transcriptBudget
    gcongr
  calc
    _ ≤ (LENGTH : ℝ) *
        (16 * ((budget + ((4224+576*LENGTH)*(9*LENGTH)+64 + budget) + 8 : Nat) : ℝ) / 2^256) := by
      gcongr
    _ ≤ _ := by
      norm_num [LENGTH, LOG_LENGTH, HIDING_SECURITY_BITS, Nat.cast_add, Nat.cast_mul]
      nlinarith [Nat.cast_nonneg (α := ℝ) budget]

/-- Conditional on each reachable first-stage transcript, the fixed-message
hybrid bound applies with at most the original shared public-query budget. -/
theorem staged_hiding_distance {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (stagedHiding permutation adversary false) (stagedHiding permutation adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
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
  have distance := reference_observation_distance permutation result.2 keys covered
    result.1.message₀ result.1.message₁ result.1.positions agree
    (adversary.observe result.1.aux) budget
    (staged_observe_query_bound permutation adversary bounded result reached)
  exact distance.trans (hiding_loss_le_target result.1.positions keys.card budget size)

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
