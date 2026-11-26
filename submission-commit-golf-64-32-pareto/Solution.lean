import CommitGolfCandidate.C3HidingScheme
import CommitGolfCandidate.R1bNarrowLane
import CommitGolfCandidate.R1bRoutes
import CommitGolfCandidate.R1bHonestCarry
import CommitGolfCandidate.R1bCarrier
import CommitGolfCandidate.C3XReplay238
import CommitGolfCandidate.C3CommitMeaning
import CommitGolfCandidate.TwoPermutationPackedAssembly
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate

namespace CommitGolf.Challenge
open TwoPermutationPrototype

set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def submission : CommitGolf.Submission := RV64.packedSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : CommitGolf.Certificate submission 67489 1318347295 80959 := by
  let leaves := RV64.C3Leaves.c3Leaves
  let meaning := RV64.C3Leaves.c3Meaning
  let opening := PackedCertificate.packed_opening_facts (RV64.packedVerifiedTranscript leaves meaning)
  have privacy := Sampling.scheme_hiding_of_c3_transcript submission.scheme TwoPermutationPrototype.Hybrid.wireBuilder
    opening.refines
  exact PackedCertificate.packed_certificate leaves meaning
    (Packed.Checker.executable_checker_facts Sampling.c3_replay_bound_238) privacy

end CommitGolf.Challenge
