import CommitGolfCandidate.Properties
import CommitGolfCandidate.Binding
import CommitGolfCandidate.Execution
import CommitGolfCandidate.OpeningInput
import CommitGolfCandidate.CheckInput
import CommitGolfCandidate.Budgets
import CommitGolfCandidate.CheckAcceptance

/-! Initial machine implementation. The full certificate is not yet proved: the
comparator must reject this draft until full machine refinement, completeness, binding,
and hiding have been established. Admission, successful honest machine runs, termination,
honest query budgets, proof size, and the declared prover-cycle bounds are proved.
No admission bypass or assumed proof is supplied. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolfCandidate.submission

end CommitGolf.Challenge
