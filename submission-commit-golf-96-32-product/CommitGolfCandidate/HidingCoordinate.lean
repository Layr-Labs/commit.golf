import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingLeafReplacement

/-! Replace one unopened message coordinate in the complete public transcript.
The other salts are sampled first; the isolated salt is still fresh and private.
The observer sees both the root and every serialized proof byte, with the same oracle. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingCoordinateDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- Resampling one coordinate of a uniform function preserves its distribution,
also for randomized continuations. Stated generically to avoid expanding the
challenge's enormous finite salt space during elaboration. -/
theorem uniform_coordinate_bind {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] := by
  have marginal : 𝒟[do let value ← $ᵗ R
                        let values ← $ᵗ (D → R)
                        pure (Function.update values index value)] = 𝒟[$ᵗ (D → R)] := by
    simpa only [bind_pure] using evalDist_uniformSample_bind_update_map
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

def observeTranscript {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  let transcript := referenceTranscript oracle.compression message salt positions
  fixedOracleRun oracle (observe transcript.1 transcript.2)

def referenceObservation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let salt ← $ᵗ (Index → Digest)
  observeTranscript ⟨tableExtending cache table, permutation⟩ message salt positions observe

def observeExcept {α : Type} (message : Message) (salt : Index → Digest) (positions : Positions)
    (hidden : Index) (observe : Commitment → Proof → OracleComp World α) (digest : Digest) :
    OracleComp World α := do
  let transcript ← queryTranscriptExcept message salt positions hidden digest
  observe transcript.1 transcript.2

attribute [local irreducible] heapQueryBudget queryHeap queryTranscript queryTranscriptExcept

theorem observe_except_bound {α : Type} (message : Message) (salt : Index → Digest)
    (positions : Positions) (hidden : Index) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (digest : Digest) :
    PublicQueryBound (observeExcept message salt positions hidden observe digest)
      ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget) :=
  public_query_bound_bind (query_transcript_except_bound message salt positions hidden digest)
    (fun transcript => bounded transcript.1 transcript.2)

theorem observe_except_reference {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions)
    (observe : Commitment → Proof → OracleComp World α) (value : Entry) (fresh : Digest) :
    fixedOracleRun oracle
      (observeExcept message salt positions hidden observe (leafDigest oracle.compression fresh value)) =
      observeTranscript oracle (Function.update message hidden value)
        (Function.update salt hidden fresh) positions observe := by
  rw [observeExcept, fixed_oracle_run_bind, query_transcript_hidden_update oracle message salt positions hidden unopened,
    pure_bind]
  rfl

/-- The full salt vector may be sampled by drawing all other randomness before
the hidden coordinate. No salt is conditioned on the public transcript. -/
theorem reference_observation_split {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (hidden : Index) :
    𝒟[referenceObservation permutation cache message positions observe] =
      𝒟[do let salt ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Digest
           observeTranscript ⟨tableExtending cache table, permutation⟩ message
             (Function.update salt hidden fresh) positions observe] := by
  unfold referenceObservation
  trans 𝒟[do let table ← $ᵗ Compression
              let salt ← $ᵗ (Index → Digest)
              let fresh ← $ᵗ Digest
              observeTranscript ⟨tableExtending cache table, permutation⟩ message
                (Function.update salt hidden fresh) positions observe]
  · apply _root_.evalDist_bind_congr
    intro table
    exact (uniform_coordinate_bind hidden (fun salt =>
      observeTranscript ⟨tableExtending cache table, permutation⟩ message salt positions observe)).symm
  · exact distribution_bind_comm _ _ _

theorem reference_observation_update {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) :
    𝒟[referenceObservation permutation cache (Function.update message hidden value) positions observe] =
      𝒟[do let salt ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Digest
           fixedOracleRun ⟨tableExtending cache table, permutation⟩
             (observeExcept message salt positions hidden observe
               (leafDigest (tableExtending cache table) fresh value))] := by
  rw [reference_observation_split permutation cache _ positions observe hidden]
  apply _root_.evalDist_bind_congr
  intro salt
  apply _root_.evalDist_bind_congr
  intro table
  apply _root_.evalDist_bind_congr
  intro fresh
  rw [observe_except_reference _ message salt positions hidden unopened]

/-- A complete root-and-opening observation changes little when one unopened
message coordinate changes. This includes the oracle work of the honest tree. -/
theorem reference_observation_coordinate_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (hidden : Index) (unopened : hidden ∉ positions) (left right : Entry) :
    measureTVDist
      (referenceObservation permutation cache (Function.update message hidden left) positions observe)
      (referenceObservation permutation cache (Function.update message hidden right) positions observe) ≤
      16 * ((keys.card + ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256 := by
  have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Digest))
    (fun salt => do
      let table ← $ᵗ Compression
      let fresh ← $ᵗ Digest
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (observeExcept message salt positions hidden observe (leafDigest (tableExtending cache table) fresh left)))
    (fun salt => do
      let table ← $ᵗ Compression
      let fresh ← $ᵗ Digest
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (observeExcept message salt positions hidden observe (leafDigest (tableExtending cache table) fresh right)))
    (by positivity) (fun salt => cached_leaf_indistinguishable permutation cache keys covered left right
      (observeExcept message salt positions hidden observe)
      ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH + budget)
      (observe_except_bound message salt positions hidden observe budget bounded))
  simpa only [measureTVDist, reference_observation_update permutation cache message positions observe hidden unopened] using distance

end CommitGolfCandidate
