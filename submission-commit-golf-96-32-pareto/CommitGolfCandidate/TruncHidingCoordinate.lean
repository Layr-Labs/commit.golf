import CommitGolfCandidate.HidingCoordinate

import CommitGolfCandidate.TruncHidingLeafReplacement

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleComp.DeferredSampling

local instance hidingCoordinateDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 12000

set_option maxHeartbeats 800000

def observeTranscript {α : Type} (oracle : Oracle) (message : Message)
    (salt : Index → Salt) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  let transcript := referenceTranscript oracle.compression message salt positions
  fixedOracleRun oracle (observe transcript.1 transcript.2)

def referenceObservation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let salt ← $ᵗ (Index → Salt)
  observeTranscript ⟨tableExtending cache table, permutation⟩ message salt positions observe

def observeHybridTranscript {α : Type} (oracle : Oracle) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α :=
  let transcript := hybridTranscript oracle.compression positions message salt freshInit
  fixedOracleRun oracle (observe transcript.1 transcript.2)

def hybridObservationForSalt {α : Type} (permutation : Perm) (cache : CompressionCache)
    (positions : Positions) (message : Message) (salt : Index → Salt)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let table ← $ᵗ Compression
  let freshInit ← $ᵗ (Index → Digest)
  observeHybridTranscript ⟨tableExtending cache table, permutation⟩ positions message salt freshInit observe

def hybridObservation {α : Type} (permutation : Perm) (cache : CompressionCache)
    (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : ProbComp α := do
  let salt ← $ᵗ (Index → Salt)
  hybridObservationForSalt permutation cache positions message salt observe

def observeHybridExcept {α : Type} (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (observe : Commitment → Proof → OracleComp World α) (digest : Digest) :
    OracleComp World α := do
  let transcript ← queryHybridTranscriptExcept positions message salt freshInit hidden digest
  observe transcript.1 transcript.2

attribute [local irreducible] heapQueryBudget queryHeap queryTranscript queryHybridTranscriptExcept

theorem observe_hybrid_except_bound {α : Type} (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (digest : Digest) :
    PublicQueryBound (observeHybridExcept positions message salt freshInit hidden observe digest)
      ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) :=
  public_query_bound_bind (query_hybrid_transcript_except_bound positions message salt freshInit hidden digest)
    (fun transcript => bounded transcript.1 transcript.2)

theorem observe_hybrid_except_reference {α : Type} (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (unopened : hidden ∉ positions)
    (observe : Commitment → Proof → OracleComp World α) (value : Entry) (fresh : Digest) :
    fixedOracleRun oracle
      (observeHybridExcept positions message salt freshInit hidden observe
        (leafDigestFromInit oracle.compression fresh value)) =
      observeHybridTranscript oracle positions (Function.update message hidden value)
        salt (Function.update freshInit hidden fresh) observe := by
  rw [observeHybridExcept, fixed_oracle_run_bind,
    query_hybrid_transcript_hidden_update oracle positions message salt freshInit hidden unopened,
    pure_bind]
  rfl

theorem hybrid_observation_split {α : Type} (permutation : Perm) (cache : CompressionCache)
    (positions : Positions) (message : Message) (salt : Index → Salt)
    (observe : Commitment → Proof → OracleComp World α) (hidden : Index) :
    𝒟[hybridObservationForSalt permutation cache positions message salt observe] =
      𝒟[do let freshInit ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Digest
           observeHybridTranscript ⟨tableExtending cache table, permutation⟩ positions message salt
             (Function.update freshInit hidden fresh) observe] := by
  unfold hybridObservationForSalt
  trans 𝒟[do let table ← $ᵗ Compression
              let freshInit ← $ᵗ (Index → Digest)
              let fresh ← $ᵗ Digest
              observeHybridTranscript ⟨tableExtending cache table, permutation⟩ positions message salt
                (Function.update freshInit hidden fresh) observe]
  · apply _root_.evalDist_bind_congr
    intro table
    exact (uniform_coordinate_bind hidden (fun freshInit =>
      observeHybridTranscript ⟨tableExtending cache table, permutation⟩ positions message salt freshInit observe)).symm
  · exact distribution_bind_comm _ _ _

theorem hybrid_observation_update {α : Type} (permutation : Perm) (cache : CompressionCache)
    (positions : Positions) (message : Message) (salt : Index → Salt)
    (observe : Commitment → Proof → OracleComp World α)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) :
    𝒟[hybridObservationForSalt permutation cache positions (Function.update message hidden value) salt observe] =
      𝒟[do let freshInit ← $ᵗ (Index → Digest)
           let table ← $ᵗ Compression
           let fresh ← $ᵗ Digest
           fixedOracleRun ⟨tableExtending cache table, permutation⟩
             (observeHybridExcept positions message salt freshInit hidden observe
               (leafDigestFromInit (tableExtending cache table) fresh value))] := by
  rw [hybrid_observation_split permutation cache positions _ salt observe hidden]
  apply _root_.evalDist_bind_congr
  intro freshInit
  apply _root_.evalDist_bind_congr
  intro table
  apply _root_.evalDist_bind_congr
  intro fresh
  rw [observe_hybrid_except_reference _ positions message salt freshInit hidden unopened]

theorem hybrid_observation_coordinate_distance {α : Type}
    (permutation : Perm) (cache : CompressionCache) (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH))
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (message : Message) (positions : Positions) (observe : Commitment → Proof → OracleComp World α)
    (budget : Nat) (bounded : ∀ root proof, PublicQueryBound (observe root proof) budget)
    (hidden : Index) (unopened : hidden ∉ positions) (left right : Entry) :
    measureTVDist
      (hybridObservation permutation cache (Function.update message hidden left) positions observe)
      (hybridObservation permutation cache (Function.update message hidden right) positions observe) ≤
      16 * ((keys.card + ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget) + 8 : Nat) : ℝ) / 2^256 := by
  unfold hybridObservation
  apply measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Salt)) _ _ (by positivity)
  intro salt
  have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ (Index → Digest))
    (fun freshInit => do
      let table ← $ᵗ Compression
      let fresh ← $ᵗ Digest
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (observeHybridExcept positions message salt freshInit hidden observe
          (leafDigestFromInit (tableExtending cache table) fresh left)))
    (fun freshInit => do
      let table ← $ᵗ Compression
      let fresh ← $ᵗ Digest
      fixedOracleRun ⟨tableExtending cache table, permutation⟩
        (observeHybridExcept positions message salt freshInit hidden observe
          (leafDigestFromInit (tableExtending cache table) fresh right)))
    (by positivity) (fun freshInit => cached_leaf_indistinguishable permutation cache keys covered left right
      (observeHybridExcept positions message salt freshInit hidden observe)
      ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH + budget)
      (observe_hybrid_except_bound positions message salt freshInit hidden observe budget bounded))
  simpa only [measureTVDist, hybrid_observation_update permutation cache positions message salt observe hidden unopened] using distance

end CommitGolfCandidate.Trunc
