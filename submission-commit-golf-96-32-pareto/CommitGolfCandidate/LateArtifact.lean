import CommitGolf.Artifact
import CommitGolf.Statements
import CommitGolfCandidate.LateWideChecker
import CommitGolfCandidate.LateCode

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv

/-- Auxiliary wide-checker execution for the Stage 2 proofs.
Commit and opening use the Stage 3 images; the public certificate uses the parsed artifact. -/
def submission : Submission := { Artifact.submission with image := fun
  | .check => Wide.image
  | .commit => Artifact.submission.image .commit
  | .opening => Artifact.submission.image .opening }

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem admission : submission.Admission := by
  intro p
  cases p <;> decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem commit_image_matches : submission.image .commit = commitImage := by rfl

end CommitGolfCandidate.Late
