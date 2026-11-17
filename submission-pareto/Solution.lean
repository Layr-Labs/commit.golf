import CommitGolfCandidate.NonceCertificate
import CommitGolf.Artifact
import CommitGolfCandidate.CapPackedImageEquality

/-! Concrete nonce-packed cap multiproof certificate. The security scheme and
resource bounds come from these executable images, which are compared with
the exact independently generated manifest artifact below. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.nonceCompressedProgram

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  exact CommitGolfCandidate.nonce_packed_submission_matches

theorem certificate : CommitGolf.Certificate submission 72704 1728053684 99225 :=
  CommitGolfCandidate.nonce_certificate

end CommitGolf.Challenge
