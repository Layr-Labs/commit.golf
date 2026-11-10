import CommitGolfCandidate.CapProbe

/-! Lazy-cache preservation for the complete paid cap detector. Earlier probe
replies survive the entire second replay and probe, not merely its final
reread. The cache never replaces an already sampled compression answer. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option autoImplicit false

theorem cap_compression_run_preserves {α : Type} (permutation : Perm)
    (computation : OracleComp World α) (cache : CompressionCache)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∀ input answer, cache input=some answer → result.2 input=some answer := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    rw [compression_run_pure] at reached
    have same := eq_of_mem_support_pure (value,cache) reached
    subst result
    exact fun _ _ stored => stored
  | query_bind query next ih =>
    cases query with
    | inl coins =>
      rw [compression_run_private] at reached
      obtain ⟨answer,_,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer cache result tail
    | inr publicQuery =>
      cases publicQuery with
      | inl input =>
        rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          exact ih answer cache result reached
        | none =>
          rw [cached] at reached
          obtain ⟨answer,_,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
          have preserved := ih answer (cache.cacheQuery input answer) result tail
          intro key value stored
          apply preserved key value
          by_cases same : key=input
          · subst key
            rw [cached] at stored
            contradiction
          · rw [QueryCache.cacheQuery_of_ne _ _ same]
            exact stored
      | inr permQuery =>
        cases permQuery with
        | inl input =>
          rw [compression_run_permute] at reached
          exact ih (permutation input) cache result reached
        | inr input =>
          rw [compression_run_inverse] at reached
          exact ih (permutation.symm input) cache result reached

theorem cap_probe_batch_cache (permutation : Perm)
    (records : List CapLowerRecord) (proof : List Digest) (root : Digest)
    (cache : CompressionCache) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support
      (compressionRun permutation (capProbeBatch records proof root) cache)) :
    ∀ reply ∈ result.1, result.2 reply.1=some reply.2 := by
  rw [capProbeBatch,compression_run_bind] at reached
  obtain ⟨⟨outcome,afterReplay⟩,_,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
  exact (probe_inputs_cache permutation
    ((outcome.getD []).take (25*records.length+127)) afterReplay result tail).2

theorem cap_probe_pair_cache (permutation : Perm)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (cache : CompressionCache) (result : CompressionReplies × CompressionCache)
    (reached : result ∈ support (compressionRun permutation
      (capProbePair leftRecords rightRecords leftProof rightProof root) cache)) :
    ∀ reply ∈ result.1, result.2 reply.1=some reply.2 := by
  rw [capProbePair,compression_run_bind] at reached
  obtain ⟨⟨left,afterLeft⟩,leftReached,tail⟩ := (mem_support_bind_iff _ _ _).mp reached
  dsimp only at tail
  rw [compression_run_bind] at tail
  obtain ⟨⟨right,afterRight⟩,rightReached,returned⟩ :=
    (mem_support_bind_iff _ _ _).mp tail
  dsimp only at returned
  rw [compression_run_pure] at returned
  have same := eq_of_mem_support_pure (left++right,afterRight) returned
  subst result
  have leftStored := cap_probe_batch_cache permutation leftRecords leftProof root
    cache (left,afterLeft) leftReached
  have rightStored := cap_probe_batch_cache permutation rightRecords rightProof root
    afterLeft (right,afterRight) rightReached
  have preserved := cap_compression_run_preserves permutation
    (capProbeBatch rightRecords rightProof root) afterLeft (right,afterRight) rightReached
  intro reply member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact preserved reply.1 reply.2 (leftStored reply leftMember)
  · exact rightStored reply rightMember

end CommitGolfCandidate
