import CommitGolf.Artifact
import CommitGolf.Statements
import CommitGolfCandidate.LateCode

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv

abbrev submission := Artifact.submission

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem admission : submission.Admission := by
  intro p
  cases p <;> decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem commit_image_matches : submission.image .commit = commitImage := by rfl

end CommitGolfCandidate.Late
