import CommitGolfCandidate.S4Extractor
import CommitGolfCandidate.TruncBirthday

import CommitGolfCandidate.LateProbe

namespace CommitGolfCandidate.S4

open Late (submission)
open Late.Check (CompressionReplies probeInputs probe_inputs_bound probe_inputs_run probe_inputs_cache compression_run_bind)
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

set_option maxRecDepth 12000

set_option maxHeartbeats 500000

def InputCollision (H : Compression) (xs : List (BitVec COMPRESSION_INPUT_LENGTH)) : Prop :=
  ∃ x∈xs, ∃ y∈xs, x≠y ∧ low240 (H x)=low240 (H y)

def ProjectedReplies (rs : CompressionReplies) : Prop :=
  ∃ x∈rs, ∃ y∈rs, x.1≠y.1 ∧ low240 x.2=low240 y.2

theorem repliesOfInputs (H : Compression) (xs : List (BitVec COMPRESSION_INPUT_LENGTH)) (h : InputCollision H xs) :
    ProjectedReplies (xs.map fun x=>(x,H x)) := by
  obtain ⟨x,hx,y,hy,d,eqn⟩:=h
  exact ⟨(x,H x),List.mem_map_of_mem hx,(y,H y),List.mem_map_of_mem hy,d,eqn⟩

private theorem costLimit (input : CheckInput) : extractCost input ≤ 5436 := by unfold extractCost; split <;> decide

noncomputable def trunc_replayClaim (claim : Scheme.Claim) :
    OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let left ← (extractRecord (claimLeft claim) (selectedRecords claim).1).code
  let right ← (extractRecord (claimRight claim) (selectedRecords claim).2).code
  return left ++ right

def trunc_replayClaimCost (claim : Scheme.Claim) : Nat :=
  extractCost (claimLeft claim) + extractCost (claimRight claim)

theorem trunc_replay_claim_cost_le (claim : Scheme.Claim) : trunc_replayClaimCost claim ≤ 10872 := by
  unfold trunc_replayClaimCost
  have h1 := costLimit (claimLeft claim)
  have h2 := costLimit (claimRight claim)
  omega

noncomputable def trunc_claimInputs (compress : Compression) (claim : Scheme.Claim) :
    List (BitVec COMPRESSION_INPUT_LENGTH) :=
  authInputs compress (claimLeft claim) (selectedRecords claim).1 ++
    authInputs compress (claimRight claim) (selectedRecords claim).2

theorem trunc_replay_claim_run (oracle : Oracle) (claim : Scheme.Claim) :
    oracle.run (trunc_replayClaim claim) =
      pure (trunc_claimInputs oracle.compression claim, trunc_replayClaimCost claim) := by
  simp only [trunc_replayClaim, oracle_run_bind, extractRun, pure_bind,
    oracle_run_pure, trunc_claimInputs, trunc_replayClaimCost, Nat.add_zero]

theorem trunc_breaks_replay_collision (sound : CheckSound) (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : Late.submission.scheme.Breaks oracle claim) :
    InputCollision oracle.compression (trunc_claimInputs oracle.compression claim) := by
  obtain ⟨input, member, input', member', collision⟩ := conflict sound oracle claim breaks
    (selectedRecords claim).1 (selectedRecords claim).2
    (selected_records_conflict claim breaks.1)
  exact ⟨input, List.mem_append_left _ member, input', List.mem_append_right _ member', collision⟩

theorem trunc_replay_claim_query_bound (claim : Scheme.Claim) :
    IsTotalQueryBound (trunc_replayClaim claim) (trunc_replayClaimCost claim) := by
  unfold trunc_replayClaim trunc_replayClaimCost
  apply isTotalQueryBound_bind ((extractRecord _ _).bound)
  intro left
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    (extractRecord (claimRight claim) (selectedRecords claim).2).bound

theorem trunc_claim_inputs_length (compress : Compression) (claim : Scheme.Claim) :
    (trunc_claimInputs compress claim).length = 56 := by
  simp only [trunc_claimInputs, List.length_append, authInputsLength]

noncomputable def trunc_boundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let result ← limitPublicQueries adversary budget
  match result with
  | none => pure []
  | some claim => do
      let inputs ← trunc_replayClaim claim
      probeInputs (inputs.take 56)

theorem trunc_bounded_collision_search_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (trunc_boundedCollisionSearch adversary budget) (budget + 10928) := by
  unfold trunc_boundedCollisionSearch
  change PublicQueryBound (_ >>= _) (budget + (10872 + 56))
  apply public_query_bound_bind (limit_public_bound _ _)
  intro result
  cases result with
  | none => trivial
  | some claim =>
    apply public_query_bound_bind
      ((public_query_bound_of_total (trunc_replay_claim_query_bound claim)).mono (trunc_replay_claim_cost_le claim))
    intro inputs
    exact (public_query_bound_of_total (probe_inputs_bound (inputs.take 56))).mono
      (List.length_take_le _ _)

theorem trunc_bounded_collision_search_run (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    oracle.run (trunc_boundedCollisionSearch adversary budget) = (do
      let (result, calls) ← oracle.run (limitPublicQueries adversary budget)
      match result with
      | none => pure ([], calls)
      | some claim => pure ((trunc_claimInputs oracle.compression claim).map
          (fun input => (input, oracle.compression input)), calls + (trunc_replayClaimCost claim + 56))) := by
  unfold trunc_boundedCollisionSearch
  rw [oracle_run_bind]
  apply bind_congr
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [oracle_run_pure]
  | some claim =>
    dsimp only
    erw [oracle_run_bind, trunc_replay_claim_run]
    simp only [pure_bind, probe_inputs_run]
    erw [List.take_of_length_le (by rw [trunc_claim_inputs_length])]
    rw [trunc_claim_inputs_length]
    erw [pure_bind]
    rfl

theorem trunc_binding_fixed_le_search (sound : CheckSound) (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => Late.submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$> (oracle.run adversary))) ≤
    (prEvent ((ProjectedReplies) <$> (fixedOracleRun oracle (trunc_boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (Late.submission.scheme.Breaks oracle)]
  simp only [fixedOracleRun, prEvent_map, Function.comp_def, trunc_bounded_collision_search_run]
  rw [OracleComp.prEvent_bind_eq_tsum]
  rw [OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [prEvent_pure]
  | some claim =>
    simp only [prEvent_pure]
    by_cases winning : Late.submission.scheme.Breaks oracle claim
    · have collision := repliesOfInputs _ _ (trunc_breaks_replay_collision sound oracle claim winning)
      simp [winning, collision]
    · simp [winning]

theorem trunc_search_reply_collision_in_cache (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (trunc_boundedCollisionSearch adversary budget) ∅))
    (collision : ProjectedReplies result.1) : ProjectedCollision result.2 := by
  unfold trunc_boundedCollisionSearch at reached
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
    refine ⟨first.1,second.1,low240 first.2,low240 second.2,different,?_,?_,heq_of_eq equal⟩
    · change (result.2 first.1).map low240=some _;rw [stored first firstMember];rfl
    · change (result.2 second.1).map low240=some _;rw [stored second secondMember];rfl

theorem trunc_binding_large_budget (adversary : Scheme.Adversary) (queryBudget : Nat)
    (large : 2 ^ BINDING_SECURITY_BITS ≤ queryBudget) :
    (prEvent ((fun (oracle, claim, calls) => Late.submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤ (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  apply le_trans (prEvent_le_one _)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ queryBudget from
    Nat.cast_le.mpr large)

theorem trunc_fixed_permutation_search_bound (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ProjectedReplies) <$> ((($ᵗ Compression) >>= fun compression =>
      fixedOracleRun ⟨compression, permutation⟩ (trunc_boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have equivalence := (EvalDistEq.of_evalDist_eq
    (compression_sampling_empty permutation (trunc_boundedCollisionSearch adversary budget))).prEvent_eq
      ProjectedReplies
  simp only [prEvent_map, Function.comp_def] at equivalence
  rw [← equivalence]
  have detected : (prEvent ((fun result => ProjectedReplies result.1) <$> (compressionRun permutation (trunc_boundedCollisionSearch adversary budget) ∅))) ≤
      (prEvent ((fun result => ProjectedCollision result.2) <$> (compressionRun permutation (trunc_boundedCollisionSearch adversary budget) ∅))) :=
    prEvent_mono_of_support _ _ _ fun result reached collision =>
      trunc_search_reply_collision_in_cache permutation adversary budget result reached collision
  have birthday := projected_collision_bound permutation (trunc_boundedCollisionSearch adversary budget)
    (budget+10928) (trunc_bounded_collision_search_bound adversary budget)
  exact detected.trans (birthday.trans (projected_cap_birthday_target budget positive small))

theorem trunc_sampled_search_bound (adversary : Scheme.Adversary) (budget : Nat)
    (positive : 1 ≤ budget) (small : budget ≤ 2 ^ BINDING_SECURITY_BITS) :
    (prEvent ((ProjectedReplies) <$> ((Oracle.sample >>= fun oracle =>
      fixedOracleRun oracle (trunc_boundedCollisionSearch adversary budget))))) ≤
      (budget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have swapped := distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm)
    (fun compression permutation => fixedOracleRun ⟨compression, permutation⟩ (trunc_boundedCollisionSearch adversary budget))
  have probabilities := (EvalDistEq.of_evalDist_eq swapped).prEvent_eq ProjectedReplies
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rw [probabilities]
  apply prEvent_bind_le_of_forall_le_of_support
  intro permutation _
  exact trunc_fixed_permutation_search_bound permutation adversary budget positive small

theorem trunc_submission_binding (sound : CheckSound) : Late.submission.scheme.Binding := by
  intro adversary budget positive
  by_cases large : 2 ^ BINDING_SECURITY_BITS ≤ budget
  · exact trunc_binding_large_budget adversary budget large
  · have reduction :
        (prEvent ((fun (oracle, claim, calls) => Late.submission.scheme.Breaks oracle claim ∧ calls ≤ budget) <$> (Scheme.bindingGame adversary))) ≤
        (prEvent ((ProjectedReplies) <$> ((Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (trunc_boundedCollisionSearch adversary budget))))) := by
      simp only [Scheme.bindingGame, bind_pure_comp]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro oracle
      apply mul_le_mul' le_rfl
      simpa only [prEvent_map, Function.comp_def] using trunc_binding_fixed_le_search sound oracle adversary budget
    exact reduction.trans (trunc_sampled_search_bound adversary budget positive (by omega))

end CommitGolfCandidate.S4
