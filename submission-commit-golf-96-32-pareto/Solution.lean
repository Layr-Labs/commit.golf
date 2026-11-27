import CommitGolfCandidate.Stage3cCheckerLaw

namespace CommitGolf.Challenge

def submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : Certificate submission 67840 911200264 186934 :=
  CommitGolfCandidate.Chained.BinaryMachine.Check.certified

end CommitGolf.Challenge
