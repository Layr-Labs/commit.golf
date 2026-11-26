import CommitGolfCandidate.HidingSecurity

import CommitGolfCandidate.TruncHidingGameIntegration

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleComp.DeferredSampling

set_option maxRecDepth 12000

set_option maxHeartbeats 800000

local instance {α : Type} : MeasurableSpace α := ⊤

attribute [local irreducible] heapQueryBudget

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

theorem referencePrivacy {State Output : Type} {k t : Nat}
    (a : Hiding.HidingAdversary State Output k) (bound : Hiding.QueryBound a t) :
    measureTVDist (Oracle.sample >>= fun o=>referenceHiding o a false)
      (Oracle.sample >>= fun o=>referenceHiding o a true) ≤ HIDING_ERROR k t := by
  apply le_min (measureTVDist_le_one _ _) ?_
  have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm)
    (fun p=>stagedHiding p a false) (fun p=>stagedHiding p a true) (by positivity)
    (fun p=>staged_hiding_distance p a bound)
  simpa only [measureTVDist,hiding_staged_distribution] using d

end CommitGolfCandidate.Trunc
