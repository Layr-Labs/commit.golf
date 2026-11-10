import CommitGolfCandidate.CapExperimentalABI
import CommitGolf.Statements

/-! Static validity and declared fuel of the actual cap images. Dynamic
execution, byte refinement and security are separate certificate fields. -/
namespace CommitGolfCandidate
open CommitGolf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem cap_program_admission : capProgram.Admission := by
  intro program
  cases program <;> decide

end CommitGolfCandidate
