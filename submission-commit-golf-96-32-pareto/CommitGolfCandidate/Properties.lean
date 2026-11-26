import CommitGolfCandidate.Programs
import CommitGolf.Statements

/-! Proved static properties of the submitted images. -/
set_option maxRecDepth 32768

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv

private theorem commit_code_length : (submission.image .commit).code.length = 796 := by
  change (assemble (commitCode LOG_LENGTH)).length = 796
  rw [assemble_length]
  decide

private theorem opening_code_length : (submission.image .opening).code.length = 97 := by
  change (assemble (openingCode LOG_LENGTH)).length = 97
  rw [assemble_length]
  decide

private theorem check_code_length : (submission.image .check).code.length = 222 := by
  change (assemble (checkCode LOG_LENGTH)).length = 222
  rw [assemble_length]
  decide

private theorem submission_layout_valid :
    LayoutValid (submission.layout.buffers submission.sizes) ⟨[], []⟩ := by
  decide

theorem submission_admission : submission.Admission := by
  intro program
  have hlayout : LayoutValid (submission.layout.buffers submission.sizes) (submission.image program) := by
    have hd : (submission.image program).data = [] := by cases program <;> rfl
    simpa only [LayoutValid, dataBase, hd] using submission_layout_valid
  cases program
  · refine ⟨⟨?_, hlayout⟩, by decide, by decide⟩
    change 4 * (submission.image .commit).code.length + 0 < MAX_PROGRAM_BYTES
    rw [commit_code_length]; decide
  · refine ⟨⟨?_, hlayout⟩, by decide, by decide⟩
    change 4 * (submission.image .opening).code.length + 0 < MAX_PROGRAM_BYTES
    rw [opening_code_length]; decide
  · refine ⟨⟨?_, hlayout⟩, by decide, by decide⟩
    change 4 * (submission.image .check).code.length + 0 < MAX_PROGRAM_BYTES
    rw [check_code_length]; decide

theorem batch_proof_bytes : openingProofBytes BATCH = 75776 := by
  decide

/-- Four leaf calls and one internal-node call per leaf, except at the root. -/
theorem commit_queries_fit : 5 * LENGTH - 1 ≤ COMMIT_BUDGET := by
  norm_num [LENGTH, LOG_LENGTH, COMMIT_BUDGET]

theorem check_queries_fit (positions : Nat) :
    (4 + LOG_LENGTH) * positions ≤ CHECK_BUDGET positions := by
  simp only [LOG_LENGTH, CHECK_BUDGET]
  omega

end CommitGolfCandidate
