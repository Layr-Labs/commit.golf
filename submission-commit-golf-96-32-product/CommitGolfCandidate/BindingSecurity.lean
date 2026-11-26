import CommitGolfCandidate.Probability
import CommitGolfCandidate.BindingProbe

/-! Full binding proof for the submitted machine images. The reduction uses at
most the adversary's public budget plus 340 compression calls, including the
reply-recording pass. This overhead is only in the security proof. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-- The replay and reply-recording overhead fits the gap between 256-bit
compression outputs and the challenge's 120-bit binding target. -/
theorem detector_birthday_le_binding_target (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((budget : ENNReal) + 340) ^ 2 / 2 ^ 256 ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have quadratic := Nat.mul_le_mul_left budget small
  have arithmetic : (budget + 340) ^ 2 ≤ budget * 2 ^ 136 := by
    change budget ≤ 2 ^ 120 at small
    change budget * budget ≤ budget * 2 ^ 120 at quadratic
    have constant : 115600 ≤ 115600 * budget := by omega
    have gap : budget * 2 ^ 120 + 116280 * budget ≤ budget * 2 ^ 136 := by
      have : 2 ^ 120 + 116280 ≤ 2 ^ 136 := by norm_num
      nlinarith
    nlinarith
  have castBound : ((budget : ENNReal) + 340) ^ 2 ≤ (budget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast arithmetic
  calc
    _ ≤ (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 := ENNReal.div_le_div_right castBound _
    _ = _ := by
      change (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (budget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

/-- Bound the detector for every fixed permutation; its inverse remains
available, as do unrestricted private coins. -/
theorem fixed_permutation_search_bound (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((($ᵗ Compression) >>= fun compression =>
      fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have equivalence := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty permutation (boundedCollisionSearch adversary budget))).prEvent_eq
      ReplyCollision
  simp only [prEvent_map, Function.comp_def] at equivalence
  rw [← equivalence]
  have detected : (prEvent ((fun result => ReplyCollision result.1) <$> (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))) ≤
      (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))) :=
    prEvent_mono_of_support _ _ _ fun result reached collision =>
      search_reply_collision_in_cache permutation adversary budget result reached collision
  have birthday := compression_collision_bound permutation (boundedCollisionSearch adversary budget)
    (budget + 340) (bounded_collision_search_bound adversary budget)
  have loose : (((budget + 340) * (budget + 340 - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) ≤
      ((budget : ENNReal) + 340) ^ 2 / 2 ^ 256 := by
    apply ENNReal.div_le_div
    · have product : (budget + 340) * (budget + 340 - 1) ≤ (budget + 340) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast product
    · calc (2 : ENNReal) ^ 256 ≤ 2 ^ 256 + 2 ^ 256 := le_self_add
           _ = 2 * 2 ^ 256 := (two_mul _).symm
  exact detected.trans (birthday.trans (loose.trans (detector_birthday_le_binding_target budget positive small)))

/-- Averaging over the independently sampled permutation preserves the bound. -/
theorem sampled_search_bound (adversary : Scheme.Adversary) (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have swapped := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (boundedCollisionSearch adversary budget))
  have probabilities := (EvalDistEq.of_evalDist_eq swapped).prEvent_eq ReplyCollision
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support
  intro permutation _
  exact fixed_permutation_search_bound permutation adversary budget positive small

/-- The submitted machine scheme meets the complete binding requirement against
all classical adversaries and all positive public-query budgets. -/
theorem submission_binding : submission.scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · exact binding_large_budget adversary budget large
  · have reduction :
        (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ budget) <$> (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (boundedCollisionSearch adversary budget))))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using binding_fixed_le_search oracle adversary budget
    exact reduction.trans (sampled_search_bound adversary budget positive (by omega))

end CommitGolfCandidate
