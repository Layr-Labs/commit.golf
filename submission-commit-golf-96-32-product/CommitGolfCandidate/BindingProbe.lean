import CommitGolfCandidate.BindingReduction
import CommitGolfCandidate.CompressionSampling

/-! A collision detector whose output contains the actual oracle replies, so its
winning event no longer needs access to the hidden full compression table.
The reduction rereads the 64 replay inputs. Its 128-call overhead is proof-only;
the submitted images, their execution costs, and the score are unchanged. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def probeInputs : List (BitVec COMPRESSION_INPUT_LENGTH) → OracleComp World CompressionReplies
  | [] => pure []
  | input :: rest => do
      let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let replies ← probeInputs rest
      return (input, answer) :: replies

/-- A collision witnessed by returned input/reply pairs alone. -/
def ReplyCollision (replies : CompressionReplies) : Prop :=
  ∃ first ∈ replies, ∃ second ∈ replies, first.1 ≠ second.1 ∧ first.2 = second.2

theorem probe_inputs_run (oracle : Oracle) (inputs : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    oracle.run (probeInputs inputs) =
      pure (inputs.map (fun input => (input, oracle.compression input)), inputs.length) := by
  induction inputs with
  | nil => exact oracle_run_pure _ _
  | cons input rest ih =>
    simp only [probeInputs]
    erw [oracle_run_public_bind oracle (.inl input)]
    rw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure, List.length_cons]
    change (pure ((input, oracle.compression input) :: rest.map (fun x => (x, oracle.compression x)),
      1 + rest.length) : ProbComp (CompressionReplies × Nat)) = pure ((input, oracle.compression input) :: rest.map (fun x => (x, oracle.compression x)),
      rest.length + 1)
    rw [Nat.add_comm 1]
    rfl

theorem probe_inputs_bound (inputs : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    IsTotalQueryBound (probeInputs inputs) inputs.length := by
  induction inputs with
  | nil => trivial
  | cons input rest ih =>
    simp only [probeInputs, bind_pure_comp]
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by simp, fun answer => ?_⟩
    simpa only [List.length_cons, Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih

theorem reply_collision_of_inputs (compress : Compression) (inputs : List (BitVec COMPRESSION_INPUT_LENGTH))
    (collision : HasCompressionCollision compress inputs) :
    ReplyCollision (inputs.map fun input => (input, compress input)) := by
  obtain ⟨first, firstMember, second, secondMember, different, equal⟩ := collision
  exact ⟨(first, compress first), List.mem_map_of_mem firstMember,
    (second, compress second), List.mem_map_of_mem secondMember, different, equal⟩

theorem claim_inputs_length (compress : Compression) (claim : Scheme.Claim) :
    (claimInputs compress claim).length = 64 := by
  simp only [claimInputs, List.length_append, record_inputs_length]

/-- Bound the original adversary, replay two records, and read their replies.
The take is redundant for every fixed oracle but supplies a syntactic bound for
all continuations of the reduction, including unreachable ones. -/
noncomputable def boundedCollisionSearch (adversary : Scheme.Adversary) (budget : Nat) :
    OracleComp World CompressionReplies := do
  let result ← limitPublicQueries adversary budget
  match result with
  | none => pure []
  | some claim => do
      let inputs ← replayClaim claim
      probeInputs (inputs.take 64)

theorem bounded_collision_search_bound (adversary : Scheme.Adversary) (budget : Nat) :
    PublicQueryBound (boundedCollisionSearch adversary budget) (budget + 128) := by
  unfold boundedCollisionSearch
  change PublicQueryBound (_ >>= _) (budget + (64 + 64))
  apply public_query_bound_bind (limit_public_bound _ _)
  intro result
  cases result with
  | none => trivial
  | some claim =>
    apply public_query_bound_bind (public_query_bound_of_total (replay_claim_query_bound claim))
    intro inputs
    exact (public_query_bound_of_total (probe_inputs_bound (inputs.take 64))).mono
      (List.length_take_le _ _)

theorem bounded_collision_search_run (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    oracle.run (boundedCollisionSearch adversary budget) = (do
      let (result, calls) ← oracle.run (limitPublicQueries adversary budget)
      match result with
      | none => pure ([], calls)
      | some claim => pure ((claimInputs oracle.compression claim).map
          (fun input => (input, oracle.compression input)), calls + 128)) := by
  unfold boundedCollisionSearch
  rw [oracle_run_bind]
  apply bind_congr
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [oracle_run_pure]
  | some claim =>
    dsimp only
    erw [oracle_run_bind, replay_claim_run]
    simp only [pure_bind, probe_inputs_run]
    erw [List.take_of_length_le (by rw [claim_inputs_length])]
    rw [claim_inputs_length]
    erw [pure_bind]
    rfl

theorem binding_fixed_le_search (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    (prEvent ((fun result => submission.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget) <$> (oracle.run adversary))) ≤
    (prEvent ((ReplyCollision) <$> (fixedOracleRun oracle (boundedCollisionSearch adversary budget)))) := by
  classical
  rw [← limit_public_probability oracle adversary budget (submission.scheme.Breaks oracle)]
  simp only [fixedOracleRun, prEvent_map, Function.comp_def, bounded_collision_search_run]
  rw [OracleComp.prEvent_bind_eq_tsum]
  rw [OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨result, calls⟩
  cases result with
  | none => simp [prEvent_pure]
  | some claim =>
    simp only [prEvent_pure]
    by_cases winning : submission.scheme.Breaks oracle claim
    · have collision := reply_collision_of_inputs _ _ (breaks_replay_collision oracle claim winning)
      simp [winning, collision]
    · simp [winning]

/-- The cache runner respects monadic sequencing, retaining the intermediate cache. -/
theorem compression_run_bind (permutation : Perm) {α β : Type} (first : OracleComp World α)
    (next : α → OracleComp World β) (cache : CompressionCache) :
    compressionRun permutation (first >>= next) cache = (do
      let (value, after) ← compressionRun permutation first cache
      compressionRun permutation (next value) after) := by
  simp [compressionRun, simulateQ_bind, StateT.run_bind]

theorem compression_run_map (permutation : Perm) {α β : Type} (f : α → β)
    (computation : OracleComp World α) (cache : CompressionCache) :
    compressionRun permutation (f <$> computation) cache =
      (fun result => (f result.1, result.2)) <$> compressionRun permutation computation cache := by
  simp [compressionRun]

/-- Every response emitted by the probe is actually present in its final cache.
The probe also preserves all entries from the starting cache. -/
theorem probe_inputs_cache (permutation : Perm) (inputs : List (BitVec COMPRESSION_INPUT_LENGTH))
    (cache : CompressionCache) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (probeInputs inputs) cache)) :
    (∀ input answer, cache input = some answer → result.2 input = some answer) ∧ ∀ reply ∈ result.1, result.2 reply.1 = some reply.2 := by
  induction inputs generalizing cache result with
  | nil =>
    rw [probeInputs, compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ _ stored => stored, by simp⟩
  | cons input rest ih =>
    simp only [probeInputs, bind_pure_comp] at reached
    erw [compression_run_compress] at reached
    cases cached : cache input with
    | some answer =>
      simp only [cached, compression_run_map, support_map, Set.mem_image] at reached
      obtain ⟨tail, tailReached, rfl⟩ := reached
      obtain ⟨preserved, stored⟩ := ih cache tail tailReached
      refine ⟨preserved, ?_⟩
      intro reply member
      rcases List.mem_cons.mp member with rfl | member
      · exact preserved input answer cached
      · exact stored reply member
    | none =>
      simp only [cached, mem_support_bind_iff, compression_run_map, support_map, Set.mem_image] at reached
      obtain ⟨answer, _, tail, tailReached, rfl⟩ := reached
      obtain ⟨preserved, stored⟩ := ih (cache.cacheQuery input answer) tail tailReached
      have earlier : ∀ key value, cache key = some value → tail.2 key = some value := by
        intro key value storedBefore
        apply preserved key value
        by_cases same : key = input
        · subst key
          rw [cached] at storedBefore
          contradiction
        · rw [QueryCache.cacheQuery_of_ne _ _ same]
          exact storedBefore
      refine ⟨earlier, ?_⟩
      intro reply member
      rcases List.mem_cons.mp member with rfl | member
      · exact preserved input answer (QueryCache.cacheQuery_self cache input answer)
      · exact stored reply member

/-- A response collision returned by the complete budgeted search forces a
collision in the lazy compression cache; no table-dependent output predicate remains. -/
theorem search_reply_collision_in_cache (permutation : Perm) (adversary : Scheme.Adversary)
    (budget : Nat) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (boundedCollisionSearch adversary budget) ∅))
    (collision : ReplyCollision result.1) : CacheHasCollision result.2 := by
  unfold boundedCollisionSearch at reached
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
    have stored := (probe_inputs_cache permutation (inputs.take 64) intermediate result reached).2
    obtain ⟨first, firstMember, second, secondMember, different, equal⟩ := collision
    exact ⟨first.1, second.1, first.2, second.2, different,
      stored first firstMember, stored second secondMember, heq_of_eq equal⟩

end CommitGolfCandidate
