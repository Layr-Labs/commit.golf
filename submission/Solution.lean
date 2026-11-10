import CommitGolfCandidate.CapCertificate
import CommitGolf.Artifact

/-! Cap multiproof certificate for the delivered RISC-V images. The retained
full-path scheme remains an explicit reference for the hiding reduction; the
challenge submission below is the new cap program and matches the exact artifact. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.capProgram

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  rfl

theorem certificate : CommitGolf.Certificate submission 75776 1765802022 45000 :=
  CommitGolfCandidate.cap_certificate

end CommitGolf.Challenge
