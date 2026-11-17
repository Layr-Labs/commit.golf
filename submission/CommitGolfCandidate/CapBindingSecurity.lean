import CommitGolfCandidate.Probability
import CommitGolfCandidate.CapBindingSearch

namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

theorem cap_detector_birthday_le_binding_target (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have arithmetic : (budget + 2*capReplayCeiling)^2 ≤ budget*2^136 :=
    cap_detector_arithmetic budget positive (by simpa [BINDING_SECURITY_BITS] using small)
  have castBound : ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 ≤ (budget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast arithmetic
  calc
    _ ≤ (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 := ENNReal.div_le_div_right castBound _
    _ = _ := by
      change (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (budget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

theorem cap_fixed_permutation_search_bound (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((($ᵗ Compression) >>= fun compression =>
      fixedOracleRun ⟨compression, permutation⟩ (capBoundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have equivalence := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty permutation (capBoundedCollisionSearch adversary budget))).prEvent_eq
      ReplyCollision
  simp only [prEvent_map, Function.comp_def] at equivalence
  rw [← equivalence]
  have detected : (prEvent ((fun result => ReplyCollision result.1) <$> (compressionRun permutation (capBoundedCollisionSearch adversary budget) ∅))) ≤
      (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation (capBoundedCollisionSearch adversary budget) ∅))) :=
    prEvent_mono_of_support _ _ _ fun result reached collision =>
      cap_search_reply_collision_in_cache permutation adversary budget result reached collision
  have birthday := compression_collision_bound permutation (capBoundedCollisionSearch adversary budget)
    (budget + (2*capReplayCeiling)) (cap_bounded_collision_search_bound adversary budget)
  have loose : (((budget + (2*capReplayCeiling)) * (budget + (2*capReplayCeiling) - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) ≤
      ((budget : ENNReal) + (2*capReplayCeiling)) ^ 2 / 2 ^ 256 := by
    apply ENNReal.div_le_div
    · have product : (budget + (2*capReplayCeiling)) * (budget + (2*capReplayCeiling) - 1) ≤ (budget + (2*capReplayCeiling)) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast product
    · calc (2 : ENNReal) ^ 256 ≤ 2 ^ 256 + 2 ^ 256 := le_self_add
           _ = 2 * 2 ^ 256 := (two_mul _).symm
  exact detected.trans (birthday.trans (loose.trans (cap_detector_birthday_le_binding_target budget positive small)))

theorem cap_sampled_search_bound (adversary : Scheme.Adversary) (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (capBoundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have swapped := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (capBoundedCollisionSearch adversary budget))
  have probabilities := (EvalDistEq.of_evalDist_eq swapped).prEvent_eq ReplyCollision
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support
  intro permutation _
  exact cap_fixed_permutation_search_bound permutation adversary budget positive small

theorem cap_program_binding : capProgram.scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · apply le_trans (prEvent_le_one _)
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity))
      (Or.inl (by finiteness))).mpr
    simpa using (show ((2^BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ budget from
      Nat.cast_le.mpr large)
  · have reduction :
        (prEvent ((fun (oracle, claim, calls) => capProgram.scheme.Breaks oracle claim ∧ calls ≤ budget) <$> (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (capBoundedCollisionSearch adversary budget))))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using cap_binding_fixed_le_search oracle adversary budget
    exact reduction.trans (cap_sampled_search_bound adversary budget positive (by omega))

end CommitGolfCandidate
