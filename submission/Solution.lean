import CommitGolfCandidate.Compact.Certificate
import CommitGolfCandidate.Compact.Artifact

/-! Certified 24-byte-nonce opening format. All resource, correctness and security
requirements below concern these same delivered RISC-V images. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 48525 :=
  CommitGolfCandidate.Compact.certificate
end CommitGolf.Challenge
