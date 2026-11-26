import CommitGolfCandidate.LateExtractor
import CommitGolfCandidate.LateProbe

namespace CommitGolfCandidate.Late.Check
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
set_option maxRecDepth 12000
set_option maxHeartbeats 500000

private theorem costLimit (input : CheckInput) : cost input ≤ 5436 := by unfold cost; split <;> decide

noncomputable def pair_replayClaim (claim : Scheme.Claim) :
    OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let left ← extract (leftInput claim) (disputed claim).1
  let right ← extract (rightInput claim) (disputed claim).2
  return left ++ right

def pair_replayClaimCost (claim : Scheme.Claim) : Nat :=
  cost (leftInput claim) + cost (rightInput claim)

theorem pair_replay_claim_cost_le (claim : Scheme.Claim) : pair_replayClaimCost claim ≤ 10872 := by
  unfold pair_replayClaimCost
  have h1 := costLimit (leftInput claim)
  have h2 := costLimit (rightInput claim)
  omega

noncomputable def pair_claimInputs (compress : Compression) (claim : Scheme.Claim) :
    List (BitVec COMPRESSION_INPUT_LENGTH) :=
  authInputs compress (leftInput claim) (disputed claim).1 ++
    authInputs compress (rightInput claim) (disputed claim).2

theorem pair_replay_claim_run (oracle : Oracle) (claim : Scheme.Claim) :
    oracle.run (pair_replayClaim claim) =
      pure (pair_claimInputs oracle.compression claim, pair_replayClaimCost claim) := by
  simp only [pair_replayClaim, oracle_run_bind, extract_run, pure_bind,
    oracle_run_pure, pair_claimInputs, pair_replayClaimCost, Nat.add_zero]

theorem pair_breaks_replay_collision (sound : AcceptsValid) (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : submission.scheme.Breaks oracle claim) :
    HasCompressionCollision oracle.compression (pair_claimInputs oracle.compression claim) := by
  exact breaks_collision sound oracle claim breaks

theorem pair_replay_claim_query_bound (claim : Scheme.Claim) :
    IsTotalQueryBound (pair_replayClaim claim) (pair_replayClaimCost claim) := by
  unfold pair_replayClaim pair_replayClaimCost
  apply isTotalQueryBound_bind (extract_bound _ _)
  intro left
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    extract_bound (rightInput claim) (disputed claim).2

theorem pair_claim_inputs_length (compress : Compression) (claim : Scheme.Claim) :
    (pair_claimInputs compress claim).length = 56 := by
  simp only [pair_claimInputs, List.length_append, authInputs, record_inputs_length, auth_length]

noncomputable def pair_boundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let result ← limitPublicQueries adversary budget
  match result with
  | none => pure []
  | some claim => do
      let inputs ← pair_replayClaim claim
      probeInputs (inputs.take 56)

theorem pair_bounded_collision_search_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (pair_boundedCollisionSearch adversary budget) (budget + 10928) := by
  unfold pair_boundedCollisionSearch
  change PublicQueryBound (_ >>= _) (budget + (10872 + 56))
  apply public_query_bound_bind (limit_public_bound _ _)
  intro result
  cases result with
  | none => trivial
  | some claim =>
    apply public_query_bound_bind
      ((public_query_bound_of_total (pair_replay_claim_query_bound claim)).mono (pair_replay_claim_cost_le claim))
    intro inputs
    exact (public_query_bound_of_total (probe_inputs_bound (inputs.take 56))).mono
      (List.length_take_le _ _)

theorem pair_bounded_collision_search_run (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    oracle.run (pair_boundedCollisionSearch adversary budget) = (do
      let (result, calls) ← oracle.run (limitPublicQueries adversary budget)
      match result with
      | none => pure ([], calls)
      | some claim => pure ((pair_claimInputs oracle.compression claim).map
          (fun input => (input, oracle.compression input)), calls + (pair_replayClaimCost claim + 56))) := by
  unfold pair_boundedCollisionSearch
  rw [oracle_run_bind]
  apply bind_congr
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [oracle_run_pure]
  | some claim =>
    dsimp only
    erw [oracle_run_bind, pair_replay_claim_run]
    simp only [pure_bind, probe_inputs_run]
    erw [List.take_of_length_le (by rw [pair_claim_inputs_length])]
    rw [pair_claim_inputs_length]
    erw [pure_bind]
    rfl

theorem pair_binding_fixed_le_search (sound : AcceptsValid) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$> (oracle.run adversary))) ≤
    (prEvent ((ReplyCollision) <$> (fixedOracleRun oracle (pair_boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (submission.scheme.Breaks oracle)]
  simp only [fixedOracleRun, prEvent_map, Function.comp_def, pair_bounded_collision_search_run]
  rw [OracleComp.prEvent_bind_eq_tsum]
  rw [OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [prEvent_pure]
  | some claim =>
    simp only [prEvent_pure]
    by_cases winning : submission.scheme.Breaks oracle claim
    · have collision := reply_collision_of_inputs _ _ (pair_breaks_replay_collision sound oracle claim winning)
      simp [winning, collision]
    · simp [winning]

theorem pair_search_reply_collision_in_cache (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (pair_boundedCollisionSearch adversary budget) ∅))
    (collision : ReplyCollision result.1) : CacheHasCollision result.2 := by
  unfold pair_boundedCollisionSearch at reached
  rw [compression_run_bind] at reached
  obtain ⟨⟨outcome, cache⟩, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
  cases outcome with
  | none =>
    dsimp only at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    obtain ⟨_, impossible, _⟩ := collision
    simp at impossible
  | some claim =>
    dsimp only at reached
    rw [compression_run_bind] at reached
    obtain ⟨⟨inputs, intermediate⟩, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
    have stored := (probe_inputs_cache permutation (inputs.take 56) intermediate result reached).2
    obtain ⟨first, firstMember, second, secondMember, different, equal⟩ := collision
    exact ⟨first.1, second.1, first.2, second.2, different,
      stored first firstMember, stored second secondMember, heq_of_eq equal⟩

theorem pair_binding_large_budget (adversary : Scheme.Adversary) (queryBudget : Nat)
    (large : 2 ^ BINDING_SECURITY_BITS ≤ queryBudget) :
    (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤ (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  apply le_trans (prEvent_le_one _)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ queryBudget from
    Nat.cast_le.mpr large)

theorem pair_detector_birthday_le_binding_target (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((budget : ENNReal) + 10928) ^ 2 / 2 ^ 256 ≤ (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have small120 : budget ≤ 2 ^ 120 := small
  have quadratic : budget * budget ≤ budget * 2 ^ 120 := Nat.mul_le_mul_left budget small120
  have arithmetic : (budget + 10928) ^ 2 ≤ budget * 2 ^ 136 := by
    have h1 : (budget + 10928) ^ 2 = budget * budget + 21856 * budget + 119421184 := by ring
    have h2 : 119421184 ≤ 119421184 * budget := by omega
    have h3 : budget * 2 ^ 120 + 21856 * budget + 119421184 * budget =
        budget * (2 ^ 120 + 21856 + 119421184) := by ring
    have h4 : budget * (2 ^ 120 + 21856 + 119421184) ≤ budget * 2 ^ 136 :=
      Nat.mul_le_mul_left budget (by decide)
    omega
  have castBound : ((budget : ENNReal) + 10928) ^ 2 ≤ (budget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast arithmetic
  calc
    _ ≤ (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 := ENNReal.div_le_div_right castBound _
    _ = _ := by
      change (budget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (budget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

theorem pair_fixed_permutation_search_bound (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((($ᵗ Compression) >>= fun compression =>
      fixedOracleRun ⟨compression, permutation⟩ (pair_boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have equivalence := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty permutation (pair_boundedCollisionSearch adversary budget))).prEvent_eq
      ReplyCollision
  simp only [prEvent_map, Function.comp_def] at equivalence
  rw [← equivalence]
  have detected : (prEvent ((fun result => ReplyCollision result.1) <$> (compressionRun permutation (pair_boundedCollisionSearch adversary budget) ∅))) ≤
      (prEvent ((fun result => CacheHasCollision result.2) <$> (compressionRun permutation (pair_boundedCollisionSearch adversary budget) ∅))) :=
    prEvent_mono_of_support _ _ _ fun result reached collision =>
      pair_search_reply_collision_in_cache permutation adversary budget result reached collision
  have birthday := compression_collision_bound permutation (pair_boundedCollisionSearch adversary budget)
    (budget + 10928) (pair_bounded_collision_search_bound adversary budget)
  have loose : (((budget + 10928) * (budget + 10928 - 1) : Nat) : ENNReal) / (2 * 2 ^ 256) ≤
      ((budget : ENNReal) + 10928) ^ 2 / 2 ^ 256 := by
    apply ENNReal.div_le_div
    · have product : (budget + 10928) * (budget + 10928 - 1) ≤ (budget + 10928) ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      exact_mod_cast product
    · calc (2 : ENNReal) ^ 256 ≤ 2 ^ 256 + 2 ^ 256 := le_self_add
           _ = 2 * 2 ^ 256 := (two_mul _).symm
  exact detected.trans (birthday.trans (loose.trans (pair_detector_birthday_le_binding_target budget positive small)))

theorem pair_sampled_search_bound (adversary : Scheme.Adversary) (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (pair_boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have swapped := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (pair_boundedCollisionSearch adversary budget))
  have probabilities := (EvalDistEq.of_evalDist_eq swapped).prEvent_eq ReplyCollision
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support
  intro permutation _
  exact pair_fixed_permutation_search_bound permutation adversary budget positive small

theorem pair_submission_binding (sound : AcceptsValid) : submission.scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · exact pair_binding_large_budget adversary budget large
  · have reduction :
        (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ budget) <$> (Scheme.bindingGame adversary))) ≤
        (prEvent ((ReplyCollision) <$> ((Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (pair_boundedCollisionSearch adversary budget))))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using pair_binding_fixed_le_search sound oracle adversary budget
    exact reduction.trans (pair_sampled_search_bound adversary budget positive (by omega))

end CommitGolfCandidate.Late.Check
