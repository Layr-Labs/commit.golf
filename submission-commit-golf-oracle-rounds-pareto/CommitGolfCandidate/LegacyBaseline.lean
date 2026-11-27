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
import CommitGolfCandidate.LeafResourceBridge
import CommitGolfCandidate.ResourceTests

/-! Original certificate for the serial baseline images, including adaptive binding
and commitment-and-opening hiding. The track's `Solution` module transports this
certificate through the exact legacy bridge to its full depth certificate. -/
namespace CommitGolfCandidate.LegacyBaseline

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

theorem certificate : CommitGolf.Certificate submission 102400 3959423012 48670 where
  admission := CommitGolfCandidate.submission_admission
  machineSuccess := CommitGolfCandidate.submission_machine_success
  termination := CommitGolfCandidate.submission_termination
  completeness := CommitGolfCandidate.submission_completeness
  honestBudgets := CommitGolfCandidate.submission_honest_budgets
  proofSize := CommitGolfCandidate.submission_proof_size
  proverCycles := CommitGolfCandidate.submission_prover_cycles
  binding := CommitGolfCandidate.submission_binding
  hidingProperty := CommitGolfCandidate.submission_hiding

end CommitGolfCandidate.LegacyBaseline
