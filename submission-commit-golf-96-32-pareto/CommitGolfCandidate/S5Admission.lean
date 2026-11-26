import CommitGolf.Artifact
import CommitGolf.Statements
namespace CommitGolfCandidate.S5Machine
open CommitGolf
set_option maxRecDepth 150000 in
set_option maxHeartbeats 16000000 in
theorem admission : Artifact.submission.Admission := by intro p;cases p <;> decide
end CommitGolfCandidate.S5Machine
