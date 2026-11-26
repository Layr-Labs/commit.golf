import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingHybrid

/-! Preserve the full two-stage adversary while moving its first stage to lazy
compression sampling. The selected messages, positions, retained state, and cache
stay jointly distributed, and the observing stage keeps its certified query bound. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingGameIntegrationDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

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

theorem fixed_oracle_run_coins (oracle : Oracle) {α : Type} (coins : ProbComp α) :
    fixedOracleRun oracle (liftM coins : OracleComp World α) = coins := by
  rw [fixedOracleRun, oracle_run_coins, Functor.map_map]
  exact id_map coins

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

/-- Exact transition to the cache-conditioned game; no adversary independence is
assumed and neither the cache nor the full oracle is exposed in the output. -/
theorem hiding_staged_distribution {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[($ᵗ Perm) >>= fun permutation => stagedHiding permutation adversary selectSecond] := by
  rw [hiding_reference_distribution]
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

/-- Any challenge produced by lazy oracle simulation is a possible syntactic
first-stage result, so the contract's shared query-budget promise applies to it. -/
theorem staged_observe_query_bound {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (result : Hiding.HidingChallenge State openingSize × CompressionCache)
    (reached : result ∈ support (compressionRun permutation adversary.choose ∅))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (compressionHandler permutation) adversary.choose).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (compressionHandler permutation) adversary.choose ∅ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    have projection : Prod.fst <$> Hiding.counted adversary.choose = adversary.choose :=
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩
    rw [projection]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

end CommitGolfCandidate
