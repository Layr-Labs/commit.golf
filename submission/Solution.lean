import CommitGolfCandidate.Compact.NoInitCertificate
import CommitGolfCandidate.Compact.NoInitArtifact
/-! Complete certificate and full artifact equality for the counter-free compact opening. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.noInitSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.noInit_submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 42253 :=
  CommitGolfCandidate.Compact.noInit_certificate
end CommitGolf.Challenge
