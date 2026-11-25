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

theorem batch_proof_bytes : proofBytes LOG_LENGTH BATCH = 77824 := by
  norm_num [BATCH, proofBytes, capBytes, capCount, capLog, openingBytes, LOG_LENGTH]

/-- Four leaf calls per leaf, one call per internal node above the cap, and 64 chain calls. -/
theorem commit_queries_fit : 5 * LENGTH - 64 ≤ COMMIT_BUDGET := by
  norm_num [LENGTH, LOG_LENGTH, COMMIT_BUDGET]

/-- 64 cap-chain calls plus four leaf and 17 path calls per opened position. -/
theorem check_queries_fit (positions : Nat) :
    85 * positions ≤ CHECK_BUDGET positions := by
  simp only [LOG_LENGTH, CHECK_BUDGET]
  omega

end CommitGolfCandidate
