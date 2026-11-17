import CommitGolfCandidate.TwoPermutationPackedAssembly
import CommitGolfCandidate.TwoPermutationPackedLeafCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate

namespace CommitGolf.Challenge
open TwoPermutationPrototype

def submission : CommitGolf.Submission := RV64.packedSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : CommitGolf.Certificate submission 67584 671294176 85511 :=
  PackedCertificate.packed_certificate RV64.PackedLeaves.executableLeaves
    RV64.PackedLeaves.executableMeaning Packed.Checker.executable_checker_facts

end CommitGolf.Challenge
