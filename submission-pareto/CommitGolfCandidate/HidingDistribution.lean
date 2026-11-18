import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingMachine

/-! Exact reduction of the submitted hiding game to the reference game with generated
nonces (`referenceHidingGen`, `S3HidingBase`), played by the adversary that applies the
compaction pass to the proof it observes. This is equality of distributions, not yet a
statistical-distance bound. Both adversary stages retain their original coins, public
oracle access, and shared oracle. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingDistributionDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv OracleComp OracleComp.DeferredSampling

/-- For one seed reply, the returned root and the opening of the returned trapdoor are
the reference root and the transformed reference proof under the generated, tagged salts. -/
theorem commit_final_transfer (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 256) (positions : Positions) :
    let committed := nonceCompressedProgram.readCommit (commitFinalResult oracle message answer).1
    let salt := expandTaggedVector (s4GenNonce oracle.permutation (answer.cast width))
    committed.1 = (referenceTranscript oracle.compression oracle.permutation message salt positions).1 ∧
    nonceCompressedProgram.scheme.opening committed.2 positions =
      pure (noncePostprocess positions
        (referenceTranscript oracle.compression oracle.permutation message salt positions).2) := by
  have contents := commit_final_contents oracle message answer width
  have nonces : committedNonce (commitFinalResult oracle message answer).1.state =
      s4GenNonce oracle.permutation (answer.cast width) := funext contents.2
  have root := committed_root_reference oracle message _ contents.1 positions
  have opened := opening_reference_bytes oracle message _ contents.1 positions
  rw [nonces] at root opened
  exact ⟨root, opened⟩

/-- The public transcript law of the submitted images, for every fixed oracle. -/
theorem honest_transcript_law : S3TranscriptLaw noncePostprocess :=
  s3_transcript_law noncePostprocess _ commit_salt_width
    (fun oracle message answer => commitFinalResult oracle message answer)
    (fun oracle message => (congrArg oracle.run (nonce_compressed_commit_run message)).trans
      (commit_run_distribution oracle message))
    (fun oracle message answer positions =>
      (commit_final_transfer oracle message answer (commit_salt_width message) positions).1)
    (fun oracle message answer positions =>
      (commit_final_transfer oracle message answer (commit_salt_width message) positions).2)

/-- Distributional equality for each fixed shared oracle, including the change from
the seed reply to the generated nonces. No query bound is needed here. -/
theorem hiding_fixed_reference {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) :
    𝒟[fixedOracleRun oracle
        (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond)] =
      𝒟[referenceHidingGen oracle (capTransformAdversary noncePostprocess adversary) selectSecond] :=
  s3_hiding_fixed_reference honest_transcript_law oracle adversary selectSecond

/-- The submitted hiding game and the reference game of the transformed adversary are
the same distribution. The final hiding proof bounds the distance between the selectors. -/
theorem hiding_reference_distribution {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary selectSecond)] =
      𝒟[Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary noncePostprocess adversary) selectSecond] :=
  s3_hiding_reference_distribution honest_transcript_law adversary selectSecond

/-- The exact statistical distance required by the certificate is the distance between
the reference games of the transformed adversary. -/
theorem hiding_distance_reference {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) :
    measureTVDist
      (Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary false))
      (Hiding.runHiding (Hiding.hidingExperiment nonceCompressedProgram.scheme adversary true)) =
    measureTVDist
      (Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary noncePostprocess adversary) false)
      (Oracle.sample >>= fun oracle =>
        referenceHidingGen oracle (capTransformAdversary noncePostprocess adversary) true) :=
  s3_hiding_distance_reference honest_transcript_law adversary

end CommitGolfCandidate
