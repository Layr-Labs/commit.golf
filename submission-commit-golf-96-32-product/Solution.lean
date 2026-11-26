import CommitGolfCandidate.PairFinal
import CommitGolf.Artifact

namespace CommitGolf.Challenge

def submission : Submission := CommitGolfCandidate.PairCap.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  CommitGolfCandidate.PairCap.matches_artifact

theorem certificate : Certificate submission 71680 959447084 40631 :=
  CommitGolfCandidate.PairCap.certificate_of_evaluation CommitGolfCandidate.PairCap.batchEvaluation

end CommitGolf.Challenge
