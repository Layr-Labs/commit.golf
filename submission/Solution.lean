import CommitGolfCandidate.Compact.FastOpeningCertificate
import CommitGolfCandidate.Compact.FastOpeningArtifact
/-! Complete certificate and full artifact equality for the unrolled compact opening. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.Compact.fastSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Compact.fast_submission_matches

theorem certificate : CommitGolf.Certificate submission 101376 1728053684 45453 :=
  CommitGolfCandidate.Compact.fast_certificate
end CommitGolf.Challenge
