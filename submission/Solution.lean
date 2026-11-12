import CommitGolfCandidate.CapCertificate
import CommitGolf.Artifact
import CommitGolfCandidate.CapPackedImageEquality

/-! Cap multiproof certificate for the delivered RISC-V images. The retained
full-path scheme remains an explicit reference for the hiding reduction; the
challenge submission below is the new cap program and matches the exact artifact. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.capProgram

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  exact CommitGolfCandidate.cap_packed_submission_matches

theorem certificate : CommitGolf.Certificate submission 73728 1728053684 43531 :=
  CommitGolfCandidate.cap_certificate

end CommitGolf.Challenge
