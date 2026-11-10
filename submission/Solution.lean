import CommitGolfCandidate.Properties
import CommitGolfCandidate.Binding
import CommitGolfCandidate.Execution
import CommitGolfCandidate.OpeningInput
import CommitGolfCandidate.CheckInput
import CommitGolfCandidate.Budgets
import CommitGolfCandidate.CheckAcceptance
import CommitGolfCandidate.Completeness
import CommitGolfCandidate.BindingSecurity
import CommitGolfCandidate.HidingSecurity
import CommitGolf.Artifact
import CommitGolfCandidate.PackedImageEquality
import CommitGolfCandidate.LeafResourceBridge
import CommitGolfCandidate.ResourceTests
import CommitGolfCandidate.FastOpeningCertificate
import CommitGolfCandidate.FastOpeningArtifact

/-! Certified unrolled-opening machine implementation. Every requirement below is proved
for these same RISC-V images, including adaptive binding and commitment-and-opening
hiding. The comparator replays this theorem against the fixed challenge statement. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.fastSubmission

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  exact CommitGolfCandidate.fast_submission_matches

theorem certificate : CommitGolf.Certificate submission 102400 1728053684 45453 :=
  CommitGolfCandidate.fast_certificate

end CommitGolf.Challenge
