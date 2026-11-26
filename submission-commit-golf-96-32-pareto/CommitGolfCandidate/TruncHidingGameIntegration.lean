import CommitGolfCandidate.HidingGameIntegration

import CommitGolfCandidate.TruncHidingTaggedSalt

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleComp.DeferredSampling

set_option maxRecDepth 12000

set_option maxHeartbeats 800000

local instance {α : Type} : MeasurableSpace α := ⊤

def queryActualTranscript (message : Message) (salt : Index → Salt) (positions : Positions) :
    OracleComp World (Commitment × Proof) :=
  queryTranscript (queryHeap LENGTH (queryActualLeaf message salt) LOG_LENGTH) salt positions

attribute [local irreducible] heapQueryBudget queryHeap queryTranscript

theorem query_actual_transcript_reference (oracle : Oracle) (message : Message)
    (salt : Index → Salt) (positions : Positions) :
    fixedOracleRun oracle (queryActualTranscript message salt positions) =
      pure (referenceTranscript oracle.compression message salt positions) := by
  have correct (node : Nat) (positive : 0 < node) (inside : node < 2*LENGTH) :=
    query_heap_reference oracle LENGTH (queryActualLeaf message salt)
      (actualLeafValues oracle.compression message salt) (query_actual_leaf_reference oracle message salt)
      LOG_LENGTH node positive inside (by
        change LENGTH ≤ LENGTH*node
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left LENGTH positive)
  exact query_transcript_reference oracle _ _ correct salt positions

def referenceContinuation {α : Type} (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let salt ← (liftM ($ᵗ (Index → Salt)) : OracleComp World (Index → Salt))
  let transcript ← queryActualTranscript message salt positions
  observe transcript.1 transcript.2

theorem reference_continuation_run {α : Type} (oracle : Oracle) (message : Message)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) :
    fixedOracleRun oracle (referenceContinuation message positions observe) =
      (($ᵗ (Index → Salt)) >>= fun salt => observeTranscript oracle message salt positions observe) := by
  rw [referenceContinuation, fixed_oracle_run_bind, fixed_oracle_run_coins]
  apply bind_congr
  intro salt
  rw [fixed_oracle_run_bind, query_actual_transcript_reference, pure_bind]
  rfl

def referenceExperiment {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    OracleComp World Output := do
  let challenge ← adversary.choose
  referenceContinuation (if selectSecond then challenge.message₁ else challenge.message₀)
    challenge.positions (adversary.observe challenge.aux)

theorem reference_experiment_run {State Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    fixedOracleRun oracle (referenceExperiment adversary selectSecond) =
      referenceHiding oracle adversary selectSecond := by
  rw [referenceExperiment, fixed_oracle_run_bind]
  unfold referenceHiding
  apply bind_congr
  intro challenge
  rw [reference_continuation_run]
  rfl

def stagedHiding {State Output : Type} {openingSize : Nat} (permutation : Perm)
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) : ProbComp Output := do
  let (challenge, cache) ← compressionRun permutation adversary.choose ∅
  referenceObservation permutation cache
    (if selectSecond then challenge.message₁ else challenge.message₀)
    challenge.positions (adversary.observe challenge.aux)

theorem hiding_staged_distribution {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    𝒟[Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond] =
      𝒟[($ᵗ Perm) >>= fun permutation => stagedHiding permutation adversary selectSecond] := by
  simp only [Oracle.sample, bind_assoc, pure_bind, ← reference_experiment_run]
  trans 𝒟[do let permutation ← $ᵗ Perm
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩ (referenceExperiment adversary selectSecond)]
  · exact distribution_bind_comm _ _ _
  · apply _root_.evalDist_bind_congr
    intro permutation
    rw [referenceExperiment, staged_compression_sampling]
    unfold stagedHiding referenceObservation
    apply _root_.evalDist_bind_congr
    intro result
    cases result with
    | mk challenge cache =>
      apply _root_.evalDist_bind_congr
      intro table
      rw [reference_continuation_run]

end CommitGolfCandidate.Trunc
