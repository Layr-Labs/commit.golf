import CommitGolfCandidate.S3HidingBase
import CommitGolfCandidate.OpeningInput
import CommitGolfCandidate.ParentRefinement
import CommitGolfCandidate.Probability

/-! Transfer from the real machine to the stage-3 reference game, proved once
for any commitment refinement of the stated shape. The commit machine enters
only through four facts (salt sampler, final state per reply, run law, final
contents); `HidingMachine`, `HidingDistribution` and `CapHidingSecurity`
instantiate them with the commit-output lemmas. Nothing is assumed about the
oracle: every statement holds for each fixed compression and permutation. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance s3HidingTransferDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleComp.DeferredSampling

/-- The committed-state facts used here: root slot, parent consistency, and
stage-3 leaves (two permutation calls) in every heap leaf slot. -/
def S3Committed (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = heapDigest state 4294971424 1 ∧
  HeapParents oracle.compression state 4294971424 LENGTH 0 ∧
  ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
    s3LeafDigest oracle.permutation (readNonce state (5368713248+24*index.val)) (message index)

/-- The machine heap is the reference heap with stage-3 leaves, on every used slot. -/
theorem s3_committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : S3Committed oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (node : Nat) (positive : 0 < node) (inside : node < 2*LENGTH) :
    heapDigest state 4294971424 node =
      saltedHeap oracle.compression oracle.permutation message salt node := by
  apply heap_eq_reference oracle.compression LENGTH _ _ correct.2.1 _ node positive inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

theorem s3_committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : S3Committed oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index) :
    readBuffer state submission.layout.commitment 32 =
      saltedHeap oracle.compression oracle.permutation message salt 1 :=
  correct.1.trans (s3_committed_heap_reference oracle message state correct salt salts
    1 (by decide) (by decide))

theorem s3_opening_reference_digest (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : S3Committed oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (positions : Positions) (ordinal part : Nat)
    (present : ordinal < positions.card) (inside : part < 25) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal+32*part) 32 =
    referenceOpeningDigest (saltedHeap oracle.compression oracle.permutation message salt)
      salt positions ordinal part := by
  dsimp only
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have records := opening_output_records state positions ordinal present
  by_cases zero : part = 0
  · subst part
    simpa only [referenceOpeningDigest, if_pos rfl, ite_true, Nat.mul_zero, Nat.add_zero]
      using records.1.trans (salts index)
  · have level : part-1 < LOG_LENGTH := by change part-1 < 24; omega
    have address : submission.layout.proof+800*ordinal+32*part =
        submission.layout.proof+800*ordinal+32+32*(part-1) := by omega
    rw [address, records.2 (part-1) level]
    simp only [referenceOpeningDigest, if_neg zero]
    have bounds := opening_sibling_bounds index (part-1) level
    exact s3_committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2

/-- All bytes emitted by the actual opening image equal the reference proof,
for arbitrary opening sets including the empty set. -/
theorem s3_opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : S3Committed oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, readNonce state (5368713248+24*index.val) = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression oracle.permutation message salt)
        salt positions := by
  dsimp only
  rw [Submission.readProof, opening_result_succeeded, if_pos rfl, opening_result_length]
  unfold referenceOpening
  apply List.map_congr_left
  intro offset present
  have below := List.mem_range.mp present
  have ordinal : offset/800 < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have part : (offset%800)/32 < 25 := by omega
  have address : submission.layout.proof+800*(offset/800)+32*((offset%800)/32)+offset%32 =
      submission.layout.proof+offset := by omega
  have digest := s3_opening_reference_digest oracle message state correct salt salts positions
    (offset/800) ((offset%800)/32) ordinal part
  rw [← digest, read_buffer_byte _ _ 32 (offset%32) (by omega), address]

/-- The actual commitment followed by its actual opening, returning precisely
the public transcript seen by the adversary. The private trapdoor is discarded. -/
def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← submission.scheme.commit message
  let proof ← submission.scheme.opening trapdoor positions
  return (root, proof)

private theorem scheme_commit_map (program : Submission) (message : Message) :
    program.scheme.commit message = program.readCommit <$> program.run .commit message := rfl

attribute [local irreducible] submission readBuffer saltedHeap referenceOpening

private theorem s3_final_transcript (oracle : Oracle) (message : Message) (result : Execution)
    {bits : Nat} (answer : BitVec bits)
    (contents : S3Committed oracle message result.state ∧
      ∀ index : Index, readNonce result.state (5368713248+24*index.val) =
        expandNonce192 (answer.extractLsb' (192*index.val) 192))
    (positions : Positions) :
    let (root, trapdoor) := submission.readCommit result
    (root, submission.readProof (openingResult trapdoor positions)) =
      referenceTranscript oracle.compression oracle.permutation message
        (fun index => expandNonce192 (answer.extractLsb' (192*index.val) 192)) positions := by
  apply Prod.ext
  · exact s3_committed_root_reference oracle message _ contents.1 _ contents.2
  · exact s3_opening_reference_bytes oracle message _ contents.1 _ contents.2 positions

/-- For every fixed oracle and input, the actual transcript is exactly a fresh
salt draw followed by the reference tree computation, given the commit run law. -/
theorem s3_honest_transcript_distribution (oracle : Oracle) (message : Message)
    (positions : Positions) {bits : Nat} (coins : ProbComp (BitVec bits))
    (final : BitVec bits → Execution × Nat)
    (run : oracle.run (submission.run .commit message) =
      (coins >>= fun answer => pure (final answer)))
    (contents : ∀ answer, S3Committed oracle message (final answer).1.state ∧
      ∀ index : Index, readNonce (final answer).1.state (5368713248+24*index.val) =
        expandNonce192 (answer.extractLsb' (192*index.val) 192)) :
    fixedOracleRun oracle (honestTranscript message positions) =
      (coins >>= fun answer => pure (referenceTranscript oracle.compression oracle.permutation
        message (fun index => expandNonce192 (answer.extractLsb' (192*index.val) 192)) positions)) := by
  have finish (root : Commitment) (trapdoor : submission.scheme.Trapdoor) :
      fixedOracleRun oracle (do
        let proof ← submission.scheme.opening trapdoor positions
        pure (root, proof)) =
      pure (root, submission.readProof (openingResult trapdoor positions)) := by
    have opened := opening_scheme_execution trapdoor positions
    erw [opened, pure_bind, fixed_oracle_run_pure]
  unfold honestTranscript
  rw [fixed_oracle_run_bind]
  simp only [finish]
  change (fixedOracleRun oracle (submission.scheme.commit message) >>= fun value =>
    pure (value.1, submission.readProof (openingResult value.2 positions))) = _
  rw [scheme_commit_map]
  change (fixedOracleRun oracle
    (submission.readCommit <$> submission.run .commit (message : Input submission.sizes .commit)) >>=
      fun value : Commitment × BitVec (8*submission.sizes.trapdoor) =>
        pure (value.1, submission.readProof (openingResult value.2 positions))) = _
  rw [fixed_oracle_run_map, bind_map_left]
  unfold fixedOracleRun
  rw [bind_map_left, run, bind_assoc]
  apply bind_congr
  intro answer
  simp only [pure_bind]
  congr 1
  exact s3_final_transcript oracle message (final answer).1 answer (contents answer) positions

/-- The exact per-oracle law of the public transcript: what the reference game
needs from the machine. -/
def S3TranscriptLaw : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions) {α : Type}
    (next : Commitment × Proof → ProbComp α),
    𝒟[fixedOracleRun oracle (honestTranscript message positions) >>= next] =
      𝒟[($ᵗ (Index → Nonce192)) >>= fun salt =>
        next (referenceTranscript oracle.compression oracle.permutation message
          (expandNonceVector salt) positions)]

/-- The transcript law from the commit refinement: run law, final contents, and
uniformity of the packed salt reply. -/
theorem s3_transcript_law (bits : Message → Nat) (coins : ∀ message, ProbComp (BitVec (bits message)))
    (final : Oracle → ∀ message, BitVec (bits message) → Execution × Nat)
    (run : ∀ oracle message, oracle.run (submission.run .commit message) =
      (coins message >>= fun answer => pure (final oracle message answer)))
    (contents : ∀ oracle message answer,
      S3Committed oracle message (final oracle message answer).1.state ∧
      ∀ index : Index, readNonce (final oracle message answer).1.state (5368713248+24*index.val) =
        expandNonce192 (answer.extractLsb' (192*index.val) 192))
    (salts : ∀ message {α : Type} (next : (Index → Nonce192) → ProbComp α),
      𝒟[coins message >>= fun packed => next (fun index => packed.extractLsb' (192*index.val) 192)] =
        𝒟[($ᵗ (Index → Nonce192)) >>= next]) :
    S3TranscriptLaw := by
  intro oracle message positions α next
  rw [s3_honest_transcript_distribution oracle message positions (coins message) (final oracle message)
    (run oracle message) (contents oracle message), bind_assoc]
  simp only [pure_bind]
  exact salts message (fun salt => next (referenceTranscript oracle.compression oracle.permutation
    message (expandNonceVector salt) positions))

private theorem s3_hiding_experiment_transcript {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment submission.scheme adversary selectSecond =
      (do let challenge ← adversary.choose
          let message := if selectSecond then challenge.message₁ else challenge.message₀
          let (root, proof) ← honestTranscript message challenge.positions
          adversary.observe challenge.aux root proof) := by
  simp only [Hiding.hidingExperiment, honestTranscript, bind_assoc, pure_bind]

/-- Distributional equality for each fixed shared oracle, including the change
from packed random bits to independent salts. No query bound is needed here. -/
theorem s3_hiding_fixed_reference (law : S3TranscriptLaw) {AdversaryState Output : Type}
    {openingSize : Nat} (oracle : Oracle)
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[fixedOracleRun oracle (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[referenceHiding oracle adversary selectSecond] := by
  rw [s3_hiding_experiment_transcript, fixed_oracle_run_bind]
  unfold referenceHiding
  apply _root_.evalDist_bind_congr
  intro challenge
  rw [fixed_oracle_run_bind]
  exact law oracle (if selectSecond then challenge.message₁ else challenge.message₀)
    challenge.positions (fun transcript =>
      fixedOracleRun oracle (adversary.observe challenge.aux transcript.1 transcript.2))

/-- The original hiding game and the reference game are the same distribution. -/
theorem s3_hiding_reference_distribution (law : S3TranscriptLaw) {AdversaryState Output : Type}
    {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond] := by
  unfold Hiding.runHiding
  apply _root_.evalDist_bind_congr
  intro oracle
  have same : (do
      let (output, _) ← oracle.run (Hiding.hidingExperiment submission.scheme adversary selectSecond)
      pure output) =
      fixedOracleRun oracle (Hiding.hidingExperiment submission.scheme adversary selectSecond) := by
    unfold fixedOracleRun
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    cases result
    rfl
  rw [same]
  exact s3_hiding_fixed_reference law oracle adversary selectSecond

/-- The certificate's statistical distance is the distance between the reference games. -/
theorem s3_hiding_distance_reference (law : S3TranscriptLaw) {AdversaryState Output : Type}
    {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) :
    measureTVDist
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary false))
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary true)) =
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary true) := by
  simp only [measureTVDist, s3_hiding_reference_distribution law]

/-- The reference-game bound the statistical chain proves (C2's statement shape). -/
def S3ReferenceBound : Prop :=
  ∀ {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize),
    Hiding.QueryBound adversary budget →
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS

/-- Hiding of the submitted machine images from the transcript law and the
reference-game bound, at the contract's error function. -/
theorem s3_submission_hiding (law : S3TranscriptLaw) (bound : S3ReferenceBound) :
    submission.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro openingSize budget
    unfold HIDING_ERROR
    apply le_min (by norm_num)
    positivity
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _) ?_
    exact (s3_hiding_distance_reference law adversary).trans_le (bound adversary bounded)

end CommitGolfCandidate
