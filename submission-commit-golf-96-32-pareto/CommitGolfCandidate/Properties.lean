import CommitGolfCandidate.Programs
import CommitGolf.Statements

/-! Proved static properties of the baseline images. Execution and security properties
must still be established before constructing CommitGolf.Certificate. -/
namespace CommitGolfCandidate
open CommitGolf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem submission_admission : submission.Admission := by
  intro program
  cases program <;> decide

theorem batch_proof_bytes : BATCH * openingBytes LOG_LENGTH = 102400 := by
  norm_num [BATCH, openingBytes, LOG_LENGTH]

/-- Four leaf calls and one internal-node call per leaf, except at the root. -/
theorem commit_queries_fit : 5 * LENGTH - 1 ≤ COMMIT_BUDGET := by
  norm_num [LENGTH, LOG_LENGTH, COMMIT_BUDGET]

theorem check_queries_fit (positions : Nat) :
    (4 + LOG_LENGTH) * positions ≤ CHECK_BUDGET positions := by
  simp only [LOG_LENGTH, CHECK_BUDGET]
  omega

end CommitGolfCandidate
