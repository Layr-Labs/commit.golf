import CommitGolfCandidate.TruncCertificate
import CommitGolfCandidate.TruncArtifact

namespace CommitGolf.Challenge
def submission : Submission := CommitGolfCandidate.Trunc.submission
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.Trunc.matchesArtifact
theorem certificate : Certificate submission 68096 963641394 109773 :=
  CommitGolfCandidate.Trunc.certificate

end CommitGolf.Challenge
