import CommitGolfCandidate.Compact.NoJumpCertificate
import CommitGolfCandidate.Compact.NoJumpArtifact
/-! Complete certificate and full artifact equality for the counter-free compact opening. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.noJumpSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.noJump_submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 42125 :=
  CommitGolfCandidate.Compact.noJump_certificate
end CommitGolf.Challenge
