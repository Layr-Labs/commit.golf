import CommitGolfCandidate.BindingReplay
import CommitGolfCandidate.CompressionSampling

/-! A collision detector whose output contains the actual oracle replies, so its
winning event no longer needs access to the hidden full compression table.
Probing is proof-only; the submitted images, their costs, and the score are unchanged. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

abbrev CompressionReplies := List (BitVec 512 × Digest)

def probeInputs : List (BitVec 512) → OracleComp World CompressionReplies
  | [] => pure []
  | input :: rest => do
      let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
      let replies ← probeInputs rest
      return (input, answer) :: replies

/-- A collision witnessed by returned input/reply pairs alone. -/
def ReplyCollision (replies : CompressionReplies) : Prop :=
  ∃ first ∈ replies, ∃ second ∈ replies, first.1 ≠ second.1 ∧ first.2 = second.2

theorem probe_inputs_run (oracle : Oracle) (inputs : List (BitVec 512)) :
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

theorem probe_inputs_bound (inputs : List (BitVec 512)) :
    IsTotalQueryBound (probeInputs inputs) inputs.length := by
  induction inputs with
  | nil => trivial
  | cons input rest ih =>
    simp only [probeInputs, bind_pure_comp]
    erw [isTotalQueryBound_query_bind_iff]
    refine ⟨by simp, fun answer => ?_⟩
    simpa only [List.length_cons, Nat.add_sub_cancel, IsTotalQueryBound, isQueryBound_map_iff] using ih

theorem reply_collision_of_inputs (compress : Compression) (inputs : List (BitVec 512))
    (collision : HasCompressionCollision compress inputs) :
    ReplyCollision (inputs.map fun input => (input, compress input)) := by
  obtain ⟨first, firstMember, second, secondMember, different, equal⟩ := collision
  exact ⟨(first, compress first), List.mem_map_of_mem firstMember,
    (second, compress second), List.mem_map_of_mem secondMember, different, equal⟩

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
theorem probe_inputs_cache (permutation : Perm) (inputs : List (BitVec 512))
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

end CommitGolfCandidate
