import CommitGolfCandidate.MoonCertificate
import CommitGolf.Artifact

/-! Certified machine implementation for the 96-to-32-byte compression track. Every requirement
below is proved for these same RISC-V images, including adaptive position binding and
commitment-and-opening statistical hiding. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  rfl

theorem certificate : CommitGolf.Certificate submission 70080 847977552 65740 :=
  CommitGolfCandidate.moon_certificate rfl

end CommitGolf.Challenge
