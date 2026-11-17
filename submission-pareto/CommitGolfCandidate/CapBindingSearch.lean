import CommitGolfCandidate.CapCheckClaimCollision
import CommitGolfCandidate.CapProbeCache

/-! Budgeted collision search for the actual cap scheme. The original
adversary is run once under its public-query limit, then two complete paid
batch replays and reply probes are charged. Private coins remain unrestricted.
No hidden table is used by the output collision predicate. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option autoImplicit false

def capClaimProbe (claim : Scheme.Claim) : OracleComp World CompressionReplies :=
  capProbePair (capCheckLoadedRecords (claimLeft claim))
    (capCheckLoadedRecords (claimRight claim))
    (capCheckSuffixWords (claimLeft claim) (544*claim.positions₀.card))
    (capCheckSuffixWords (claimRight claim) (544*claim.positions₁.card)) claim.root

theorem cap_claim_probe_bound (claim : Scheme.Claim) :
    (capClaimProbe claim).IsTotalQueryBound (2*capReplayCeiling) := by
  apply cap_probe_pair_ceiling
  · rw [cap_check_loaded_records_length]
    simpa [claimLeft,Index] using Finset.card_le_univ claim.positions₀
  · rw [cap_check_loaded_records_length]
    simpa [claimRight,Index] using Finset.card_le_univ claim.positions₁

noncomputable def capBoundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let outcome ← limitPublicQueries adversary budget
  match outcome with
  | none => pure []
  | some claim => capClaimProbe claim

theorem cap_bounded_collision_search_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (capBoundedCollisionSearch adversary budget)
      (budget+2*capReplayCeiling) := by
  unfold capBoundedCollisionSearch
  apply public_query_bound_bind (limit_public_bound _ _)
  intro outcome
  cases outcome with
  | none => trivial
  | some claim => exact public_query_bound_of_total (cap_claim_probe_bound claim)

theorem cap_search_reply_collision_in_cache (permutation : Perm)
    (adversary : Scheme.Adversary) (budget : Nat)
    (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation
      (capBoundedCollisionSearch adversary budget) ∅))
    (collision : ReplyCollision result.1) : CacheHasCollision result.2 := by
  rw [capBoundedCollisionSearch,compression_run_bind] at reached
  obtain ⟨⟨outcome,cache⟩,_,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
  cases outcome with
  | none =>
    dsimp only at tail
    rw [compression_run_pure] at tail
    have same := eq_of_mem_support_pure ([],cache) tail
    subst result
    obtain ⟨_,impossible,_⟩ := collision
    simp at impossible
  | some claim =>
    dsimp only [capClaimProbe] at tail
    have stored := cap_probe_pair_cache permutation _ _ _ _ _ cache result tail
    obtain ⟨first,firstMember,second,secondMember,different,equal⟩ := collision
    exact ⟨first.1,second.1,first.2,second.2,different,
      stored first firstMember,stored second secondMember,heq_of_eq equal⟩

theorem cap_binding_fixed_le_search (oracle : Oracle) (adversary : Scheme.Adversary)
    (budget : Nat) :
    (prEvent ((fun result => capProgram.scheme.Breaks oracle result.1 ∧
      result.2≤budget) <$> oracle.run adversary)) ≤
    (prEvent (ReplyCollision <$> fixedOracleRun oracle
      (capBoundedCollisionSearch adversary budget))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (capProgram.scheme.Breaks oracle)]
  simp only [fixedOracleRun,prEvent_map,Function.comp_def,capBoundedCollisionSearch,
    oracle_run_bind]
  rw [OracleComp.prEvent_bind_eq_tsum,OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome,calls⟩
  cases outcome with
  | none => simp [oracle_run_pure,prEvent_pure]
  | some claim =>
    by_cases winning : capProgram.scheme.Breaks oracle claim
    · obtain ⟨replies,probeCalls,run,collision⟩ :=
        cap_check_claim_probe_collision oracle claim winning
      change oracle.run (capClaimProbe claim)=pure (replies,probeCalls) at run
      rw [run]
      simp [prEvent_pure,winning,collision]
    · simp [winning]

end CommitGolfCandidate
