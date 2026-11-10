import CommitGolfCandidate.Compact.Machine
import CommitGolfCandidate.Compact.Budgets
import CommitGolfCandidate.Compact.Completeness
import CommitGolfCandidate.Compact.BindingSecurity
import CommitGolfCandidate.Compact.Hiding
/-! Complete certificate for one concrete compact-format submission, with 101,376 proof bytes and the proved commitment/opening cycle bounds. -/
namespace CommitGolfCandidate.Compact
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem compact_admission : submission.Admission := by
  intro program
  have old := CommitGolfCandidate.submission_admission program
  cases program with
  | commit => exact old
  | opening => exact ⟨⟨by decide,old.1.2⟩,old.2⟩
  | check => exact ⟨⟨by decide,old.1.2⟩,old.2⟩

theorem certificate : Certificate submission 101376 1728053684 48525 where
  admission := compact_admission
  machineSuccess := submission_machine_success
  termination := submission_termination
  completeness := submission_completeness
  honestBudgets := submission_honest_budgets
  proofSize := submission_proof_size
  proverCycles := submission_prover_cycles
  binding := submission_binding
  hidingProperty := compact_hiding
end CommitGolfCandidate.Compact
