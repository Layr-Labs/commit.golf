import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingMachine
import CommitGolfCandidate.HidingSalts
import CommitGolfCandidate.CompressionSampling

/-! Exact reduction of the machine hiding game to the stage-3 salted-tree
experiment `referenceHiding` (`S3HidingBase`). This is equality of
distributions, not yet a statistical-distance bound. Both adversary stages
retain their original coins, public oracle access, and shared oracle. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingDistributionDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv OracleComp OracleComp.DeferredSampling

/-- Final commitment contents in the transfer's form. -/
theorem commit_final_transfer (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) (width : bits = 192*LENGTH) :
    S3Committed oracle message (commitFinalResult oracle message answer).1.state ∧
    ∀ index : Index, readNonce (commitFinalResult oracle message answer).1.state
      (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) :=
  have contents := commit_final_contents oracle message answer width
  ⟨committed_state_transfer oracle message _ contents.1, contents.2⟩

/-- For every fixed oracle and input, the actual transcript is exactly a fresh
salt draw followed by the reference tree computation. This covers all proof bytes. -/
theorem honest_transcript_distribution (oracle : Oracle) (message : Message)
    (positions : Positions) :
    fixedOracleRun oracle (honestTranscript message positions) =
      (commitSaltCoins message >>= fun answer => pure (referenceTranscript oracle.compression
        oracle.permutation message
        (fun index => expandNonce192 (answer.extractLsb' (192*index.val) 192)) positions)) :=
  s3_honest_transcript_distribution oracle message positions (commitSaltCoins message)
    (fun answer => commitFinalResult oracle message answer) (commit_run_distribution oracle message)
    (fun answer => commit_final_transfer oracle message answer (commit_salt_width message))

/-- The public transcript law of the actual images, for every fixed oracle. -/
theorem honest_transcript_law : S3TranscriptLaw :=
  s3_transcript_law _ commitSaltCoins (fun oracle message answer => commitFinalResult oracle message answer)
    commit_run_distribution
    (fun oracle message answer => commit_final_transfer oracle message answer (commit_salt_width message))
    (fun message _ next => commit_salts_uniform message next)

/-- Distributional equality for each fixed shared oracle, including the change
from packed random bits to independent salts. No query bound is needed here. -/
theorem hiding_fixed_reference {AdversaryState Output : Type} {openingSize : Nat}
    (oracle : Oracle) (adversary : Hiding.HidingAdversary AdversaryState Output openingSize)
    (selectSecond : Bool) :
    𝒟[fixedOracleRun oracle (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[referenceHiding oracle adversary selectSecond] :=
  s3_hiding_fixed_reference honest_transcript_law oracle adversary selectSecond

/-- The original hiding game and the reference game are the same distribution.
The final hiding proof must still bound the distance between the two selectors. -/
theorem hiding_reference_distribution {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary selectSecond)] =
      𝒟[Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond] :=
  s3_hiding_reference_distribution honest_transcript_law adversary selectSecond

/-- The exact statistical distance required by the certificate is the distance
between the reference games. This transfers any proved reference bound directly
to the actual submitted RISC-V programs. -/
theorem hiding_distance_reference {AdversaryState Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary AdversaryState Output openingSize) :
    measureTVDist
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary false))
      (Hiding.runHiding (Hiding.hidingExperiment submission.scheme adversary true)) =
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary true) :=
  s3_hiding_distance_reference honest_transcript_law adversary

end CommitGolfCandidate
