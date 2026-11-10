import CommitGolfCandidate.Compact.FixedCertificate
import CommitGolfCandidate.Compact.FixedArtifact
/-! Complete certificate and full artifact equality for the counter-free compact opening. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.fixedSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.fixed_submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 39181 :=
  CommitGolfCandidate.Compact.fixed_certificate
end CommitGolf.Challenge
