import CommitGolfCandidate.Compact.SlimCertificate
import CommitGolfCandidate.Compact.SlimArtifact
/-! Complete certificate and full artifact equality for the counter-free compact opening. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.slimSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.slim_submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 42509 :=
  CommitGolfCandidate.Compact.slim_certificate
end CommitGolf.Challenge
