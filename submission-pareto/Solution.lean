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
import CommitGolfCandidate.LeafResourceBridge
import CommitGolfCandidate.ResourceTests

/-! Certified initial machine implementation. Every requirement below is proved
for these same RISC-V images, including adaptive binding and commitment-and-opening
hiding. The comparator replays this theorem against the fixed challenge statement. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  rfl

/-- Each of the 128 paths contains one salt and 24 sibling digests, all 32 bytes. -/
private def batchProofBytes : Nat := 128 * (1 + 24) * 32

/-- The opening image uses 30 fixed cycles and 380 cycles per position. -/
private def batchOpeningCycles : Nat := 30 + 128 * 380

theorem certificate : CommitGolf.Certificate submission 102400 3959423012 48670 where
  admission := CommitGolfCandidate.submission_admission
  machineSuccess := CommitGolfCandidate.submission_machine_success
  termination := CommitGolfCandidate.submission_termination
  completeness := CommitGolfCandidate.submission_completeness
  honestBudgets := CommitGolfCandidate.submission_honest_budgets
  proofSize := (CommitGolfCandidate.submission_proof_size : submission.ProofSize batchProofBytes)
  proverCycles := (CommitGolfCandidate.submission_prover_cycles : submission.ProverCycles 3959423012 batchOpeningCycles)
  binding := CommitGolfCandidate.submission_binding
  hidingProperty := CommitGolfCandidate.submission_hiding

end CommitGolf.Challenge
