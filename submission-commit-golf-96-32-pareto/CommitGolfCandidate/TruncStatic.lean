import CommitGolfCandidate.TruncImage
import CommitGolfCandidate.Properties
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem admission : submission.Admission := by intro p;cases p <;> decide

end CommitGolfCandidate.Trunc
