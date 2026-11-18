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

theorem certificate : CommitGolf.Certificate submission 69632 621224986 87559 := by
  let leaves := RV64.PackedLeaves.executableLeaves
  let meaning := RV64.PackedLeaves.executableMeaning
  let opening := PackedCertificate.packed_opening_facts (RV64.packedVerifiedTranscript leaves meaning)
  have privacy := Sampling.scheme_hiding_of_pinned_transcript submission.scheme TwoPermutationPrototype.Hybrid.builder
    opening.refines (fun adversary compress budget bounded =>
      Sampling.pinned_final_reference_hiding adversary TwoPermutationPrototype.Hybrid.builder compress budget bounded)
  exact PackedCertificate.packed_certificate leaves meaning
    (Packed.Checker.executable_checker_facts Sampling.pinned_replay_bound) privacy

end CommitGolf.Challenge
