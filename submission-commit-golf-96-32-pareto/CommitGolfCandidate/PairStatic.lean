import CommitGolfCandidate.PairImage
import CommitGolfCandidate.Properties

namespace CommitGolfCandidate.PairCap
open CommitGolf

set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem admission : submission.Admission := by
  intro p; cases p <;> decide

theorem sameCommit (m : Message) :
    submission.run .commit m = CommitGolfCandidate.submission.run .commit m := rfl

theorem sameCommitScheme (m : Message) :
    submission.scheme.commit m = CommitGolfCandidate.submission.scheme.commit m := rfl

theorem sameInitial (p : Program) (input : Input submission.sizes p) :
    submission.initialState p input = CommitGolfCandidate.submission.initialState p input := by
  cases p <;> rfl

end CommitGolfCandidate.PairCap
