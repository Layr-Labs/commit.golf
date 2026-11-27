import CommitGolfCandidate.C3PAssembly

namespace CommitGolf.Challenge
open TwoPermutationPrototype

set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def submission : CommitGolf.Submission := PackedCertificate.pairedSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : CommitGolf.Certificate submission 67489 1267884575 91600 :=
  PackedCertificate.paired_certificate

end CommitGolf.Challenge
