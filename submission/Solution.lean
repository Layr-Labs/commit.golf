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

/-! Certified initial machine implementation. Every requirement below is proved
for these same RISC-V images, including adaptive binding and commitment-and-opening
hiding. The comparator replays this theorem against the fixed challenge statement. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  exact CommitGolfCandidate.packed_submission_matches

theorem certificate : CommitGolf.Certificate submission 102400 1728053685 48525 where
  admission := CommitGolfCandidate.submission_admission
  machineSuccess := CommitGolfCandidate.submission_machine_success
  termination := CommitGolfCandidate.submission_termination
  completeness := CommitGolfCandidate.submission_completeness
  honestBudgets := CommitGolfCandidate.submission_honest_budgets
  proofSize := CommitGolfCandidate.submission_proof_size
  proverCycles := CommitGolfCandidate.submission_prover_cycles
  binding := CommitGolfCandidate.submission_binding
  hidingProperty := CommitGolfCandidate.submission_hiding

end CommitGolf.Challenge
