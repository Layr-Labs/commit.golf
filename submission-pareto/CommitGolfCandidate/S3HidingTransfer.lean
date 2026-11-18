import CommitGolfCandidate.S3HidingBase
import CommitGolfCandidate.CapHidingReduction
import CommitGolfCandidate.NonceCompressedPrograms
import CommitGolfCandidate.Probability

/-! Transfer from the submitted images to the reference game with generated nonces
(`referenceHidingGen`). The images enter only through three facts about the
commitment run for one random reply: its run law, the returned root, and the
opening of the returned trapdoor, which emits the reference proof after a pure
transformation `post` that depends only on the requested positions.
`HidingMachine` and `HidingDistribution` instantiate them. Nothing is assumed
about the oracle: every statement holds for each fixed compression and permutation. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance s3HidingTransferDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv OracleComp OracleComp.DeferredSampling

/-- The submitted commitment followed by its submitted opening, returning precisely
the public transcript seen by the adversary. The private trapdoor is discarded. -/
def honestTranscript (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, trapdoor) ← nonceCompressedProgram.scheme.commit message
  let proof ← nonceCompressedProgram.scheme.opening trapdoor positions
  return (root, proof)

/-- The reference transcript with its proof transformed by `post`. -/
def postTranscript (post : Positions → Proof → Proof) (compress : Compression)
    (permutation : Perm) (message : Message) (salt : Index → Digest) (positions : Positions) :
    Commitment × Proof :=
  let transcript := referenceTranscript compress permutation message salt positions
  (transcript.1, post positions transcript.2)

attribute [local irreducible] nonceCompressedProgram referenceTranscript

/-- For every fixed oracle and input, the actual transcript is exactly a coin draw
followed by the transformed reference transcript under the salt vector of that coin,
given the commit run law and, for each coin, the returned root and the opening of the
returned trapdoor. -/
theorem s5_honest_transcript_distribution (post : Positions → Proof → Proof)
    (oracle : Oracle) (message : Message) (positions : Positions) {Coin : Type}
    (coins : ProbComp Coin) (final : Coin → Execution × Nat) (salt : Coin → Index → Digest)
    (run : oracle.run (nonceCompressedProgram.run .commit message) =
      (coins >>= fun answer => pure (final answer)))
    (root : ∀ answer, (nonceCompressedProgram.readCommit (final answer).1).1 =
      (referenceTranscript oracle.compression oracle.permutation message (salt answer) positions).1)
    (opened : ∀ answer, nonceCompressedProgram.scheme.opening
      (nonceCompressedProgram.readCommit (final answer).1).2 positions =
        pure (post positions (referenceTranscript oracle.compression oracle.permutation message
          (salt answer) positions).2)) :
    fixedOracleRun oracle (honestTranscript message positions) =
      (coins >>= fun answer => pure (postTranscript post oracle.compression oracle.permutation
        message (salt answer) positions)) := by
  have commitRun : fixedOracleRun oracle (nonceCompressedProgram.scheme.commit message) =
      (coins >>= fun answer => pure (α := Commitment × nonceCompressedProgram.scheme.Trapdoor)
        (nonceCompressedProgram.readCommit (final answer).1)) := by
    change fixedOracleRun oracle (nonceCompressedProgram.readCommit <$>
      nonceCompressedProgram.run .commit (message : Input nonceCompressedProgram.sizes .commit)) = _
    rw [fixed_oracle_run_map]
    unfold fixedOracleRun
    rw [run, map_bind, map_bind]
    simp only [map_pure]
    rfl
  unfold honestTranscript
  rw [fixed_oracle_run_bind, commitRun, bind_assoc]
  apply bind_congr
  intro answer
  erw [pure_bind]
  change fixedOracleRun oracle (do
      let proof ← nonceCompressedProgram.scheme.opening
        (nonceCompressedProgram.readCommit (final answer).1).2 positions
      pure ((nonceCompressedProgram.readCommit (final answer).1).1, proof)) = _
  rw [opened answer, pure_bind, fixed_oracle_run_pure, root answer]
  rfl

/-- The exact per-oracle law of the public transcript: what the reference game
needs from the images. The salt vector is generated from a uniform 256-bit seed;
the opened proof is the reference proof transformed by `post`. -/
def S3TranscriptLaw (post : Positions → Proof → Proof) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions) {α : Type}
    (next : Commitment × Proof → ProbComp α),
    𝒟[fixedOracleRun oracle (honestTranscript message positions) >>= next] =
      𝒟[($ᵗ BitVec 256) >>= fun seed =>
        next (postTranscript post oracle.compression oracle.permutation message
          (expandTaggedVector (s4GenNonce oracle.permutation seed)) positions)]

/-- A uniform reply of a width proved equal to 256 is a uniform seed. -/
theorem uniform_seed_cast {bits : Nat} (width : bits = 256) {α : Type}
    (next : BitVec 256 → ProbComp α) :
    (($ᵗ BitVec bits) >>= fun answer => next (answer.cast width)) = (($ᵗ BitVec 256) >>= next) := by
  subst width
  simp only [BitVec.cast_eq]

/-- The transcript law from the commitment refinement and the opening: the random
reply is a uniform 256-bit seed, the run law, and for every reply the returned root
and the opening of the returned trapdoor under the generated, tagged salts. -/
theorem s3_transcript_law (post : Positions → Proof → Proof)
    (bits : Message → Nat) (width : ∀ message, bits message = 256)
    (final : Oracle → ∀ message, BitVec (bits message) → Execution × Nat)
    (run : ∀ oracle message, oracle.run (nonceCompressedProgram.run .commit message) =
      (($ᵗ BitVec (bits message)) >>= fun answer => pure (final oracle message answer)))
    (root : ∀ oracle message answer positions,
      (nonceCompressedProgram.readCommit (final oracle message answer).1).1 =
        (referenceTranscript oracle.compression oracle.permutation message
          (expandTaggedVector (s4GenNonce oracle.permutation (answer.cast (width message))))
          positions).1)
    (opened : ∀ oracle message answer positions,
      nonceCompressedProgram.scheme.opening
        (nonceCompressedProgram.readCommit (final oracle message answer).1).2 positions =
          pure (post positions (referenceTranscript oracle.compression oracle.permutation message
            (expandTaggedVector (s4GenNonce oracle.permutation (answer.cast (width message))))
            positions).2)) :
    S3TranscriptLaw post := by
  intro oracle message positions α next
  rw [s5_honest_transcript_distribution post oracle message positions _ (final oracle message)
    (fun answer => expandTaggedVector (s4GenNonce oracle.permutation (answer.cast (width message))))
    (run oracle message) (fun answer => root oracle message answer positions)
    (fun answer => opened oracle message answer positions), bind_assoc]
  simp only [pure_bind]
  rw [uniform_seed_cast (width message) (fun seed => next (postTranscript post oracle.compression
    oracle.permutation message (expandTaggedVector (s4GenNonce oracle.permutation seed)) positions))]

private theorem s3_hiding_experiment_transcript {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond =
      (do let challenge ← adversary.choose
          let message := if selectSecond then challenge.message₁ else challenge.message₀
          let (root, proof) ← honestTranscript message challenge.positions
          adversary.observe challenge.aux root proof) := by
  simp only [Hiding.hidingExperiment, honestTranscript, bind_assoc, pure_bind]

/-- Distributional equality for each fixed shared oracle: the submitted game is the
reference game played by the adversary that applies `post` to the proof it observes.
No query bound is needed here. -/
theorem s3_hiding_fixed_reference {post : Positions → Proof → Proof} (law : S3TranscriptLaw post)
    {AdversaryState Output : Type} {openingSize : Nat} (oracle : Oracle)
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[fixedOracleRun oracle (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond)] =
      𝒟[referenceHidingGen oracle (capTransformAdversary post adversary) selectSecond] := by
  rw [s3_hiding_experiment_transcript, fixed_oracle_run_bind]
  unfold referenceHidingGen
  simp only [capTransformAdversary, fixed_oracle_run_map, bind_map_left]
  apply _root_.evalDist_bind_congr
  intro challenge
  rw [fixed_oracle_run_bind]
  exact law oracle (if selectSecond then challenge.message₁ else challenge.message₀)
    challenge.positions (fun transcript =>
      fixedOracleRun oracle (adversary.observe challenge.aux transcript.1 transcript.2))

/-- The original hiding game and the reference game of the transformed adversary are
the same distribution. -/
theorem s3_hiding_reference_distribution {post : Positions → Proof → Proof}
    (law : S3TranscriptLaw post) {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond)] =
      𝒟[Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary post adversary) selectSecond] := by
  unfold Hiding.runHiding
  apply _root_.evalDist_bind_congr
  intro oracle
  have same : (do
      let (output, _) ← oracle.run
        (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond)
      pure output) =
      fixedOracleRun oracle (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond) := by
    unfold fixedOracleRun
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro result
    cases result
    rfl
  rw [same]
  exact s3_hiding_fixed_reference law oracle adversary selectSecond

/-- The certificate's statistical distance is the distance between the reference games
of the transformed adversary. -/
theorem s3_hiding_distance_reference {post : Positions → Proof → Proof}
    (law : S3TranscriptLaw post) {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) :
    measureTVDist
      (Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary false))
      (Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary true)) =
    measureTVDist
      (Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary post adversary) false)
      (Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary post adversary) true) := by
  simp only [measureTVDist, s3_hiding_reference_distribution law]

/-- The reference-game bound the statistical chain proves, for every adversary. -/
def S3ReferenceBound : Prop :=
  ∀ {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize),
    Hiding.QueryBound adversary budget →
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS

/-- Hiding of the submitted images from the transcript law and the reference-game
bound, at the contract's error function. The transformed adversary keeps the shared
two-stage query budget. -/
theorem s3_submission_hiding {post : Positions → Proof → Proof} (law : S3TranscriptLaw post)
    (bound : S3ReferenceBound) : nonceCompressedProgram.scheme.Hiding HIDING_ERROR := by
  constructor
  · intro openingSize budget
    unfold HIDING_ERROR
    apply le_min (by norm_num)
    positivity
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _) ?_
    exact (s3_hiding_distance_reference law adversary).trans_le
      (bound (capTransformAdversary post adversary) (cap_transform_query_bound post adversary bounded))

end CommitGolfCandidate
