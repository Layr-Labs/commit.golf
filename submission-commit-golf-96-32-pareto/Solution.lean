import CommitGolfCandidate.S4CheckLaw
import CommitGolfCandidate.S4OpeningLaw
import CommitGolfCandidate.S4Certificate

namespace CommitGolf.Challenge

def submission := CommitGolfCandidate.Late.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : Certificate submission 70410 863218785 85548 :=
  CommitGolfCandidate.S4.fromMachine CommitGolfCandidate.S4.Open.machineOpening CommitGolfCandidate.S4.Machine.machineChecker

end CommitGolf.Challenge
