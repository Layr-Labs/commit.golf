import CommitGolfCandidate.ChainedDeliveredHiding

namespace CommitGolf.Challenge
def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : CommitGolf.Certificate submission 65472 2353177256 444579 :=
  CommitGolfCandidate.Chained.Native.delivered_certificate

end CommitGolf.Challenge
