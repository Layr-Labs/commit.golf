import CommitGolfCandidate.LateSecurity
import CommitGolfCandidate.LateTransfer

namespace CommitGolfCandidate.Late
open CommitGolf

/-- The statement used by the certificate. The checked fields are attached to the
actual artifact; the remaining machine refinements are explicit premises. -/
theorem certificate_of_refinements
    (success : submission.MachineSuccess) (termination : submission.Termination)
    (complete : submission.scheme.Completeness) (budgets : submission.scheme.HonestBudgets)
    (size : submission.scheme.ProofSize 72704) (cycles : submission.ProverCycles 911802772 45875)
    (checker : Check.AcceptsValid) (refines : ViewRefinement) (late_hiding : HidingGoal) :
    Certificate submission 72704 911802772 45875 where
  admission := admission
  machineSuccess := success
  termination := termination
  completeness := complete
  honestBudgets := budgets
  proofSize := size
  proverCycles := cycles
  binding := Check.pair_submission_binding checker
  hidingProperty := machine_hiding refines late_hiding

end CommitGolfCandidate.Late
