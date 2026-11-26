import CommitGolfCandidate.MoonCertificate
import CommitGolf.Artifact

/-! Certified machine implementation for the 64-to-32-byte compression / 30-cycle permutation
track. Every requirement below is proved for these same RISC-V images, including cross-oracle
adaptive position binding and commitment-and-opening statistical hiding. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  rfl

theorem certificate : CommitGolf.Certificate submission 68512 1276210876 110258 :=
  CommitGolfCandidate.moon_certificate rfl

end CommitGolf.Challenge
