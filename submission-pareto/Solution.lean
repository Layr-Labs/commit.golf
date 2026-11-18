import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate
import CommitGolfCandidate.TwoPermutationPinnedFinalHiding
import CommitGolfCandidate.TwoPermutationPackedAssembly
import CommitGolfCandidate.TwoPermutationPackedLeafCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate

namespace CommitGolf.Challenge
open TwoPermutationPrototype

set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def submission : CommitGolf.Submission := RV64.packedSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

/-- The certificate, given the record-head facts of the honest transcripts that codec v2 needs
(`PackedCertificate.HonestHeadFacts`: opened salts below 2^123, opened leaf siblings below
2^244). -/
theorem certificate_of_head_facts (heads : PackedCertificate.HonestHeadFacts) :
    CommitGolf.Certificate submission 66800 756825559 4064915 := by
  let leaves := RV64.PackedLeaves.executableLeaves
  let meaning := RV64.PackedLeaves.executableMeaning
  let opening := PackedCertificate.packed_opening_facts (RV64.packedVerifiedTranscript leaves meaning)
  have privacy := Sampling.scheme_hiding_of_chain submission.scheme Sampling.packedBuilder opening.refines
  exact PackedCertificate.packed_certificate leaves meaning
    (Packed.Checker.executable_checker_facts heads Sampling.pinned_replay_bound) privacy

/-- Honest salts are masked to 123 bits and honest leaves cut to 244 bits, so the head facts hold. -/
theorem certificate : CommitGolf.Certificate submission 66800 756825559 4064915 :=
  certificate_of_head_facts PackedCertificate.honest_head_facts

end CommitGolf.Challenge
