import CommitGolfCandidate.NonceExpandWhole
import CommitGolfCandidate.NonceExpandCodec
import CommitGolfCandidate.NonceCheckOldTail
import CommitGolfCandidate.NonceCompressedAdmission

/-! The delivered checker agrees in exit status with the retained checker on the expanded input.
The expansion runs query-free inside the declared fuel and leaves a state equivalent to the
retained checker after its first word; the retained tail then has more fuel than it needs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

/-- One 576-byte record per position, then one 32-byte node per 32-byte footer field. -/
theorem nonce_expanded_input_length (input : CheckInput) (valid : NonceCheckValid input) :
    (nonceExpandedInput input).proof.length =
      576 * input.positions.card + 32 * ((input.proof.length - 560 * input.positions.card) / 32) := by
  have sorted : (input.positions.sort (· ≤ ·)).length = input.positions.card := Finset.length_sort _
  have size : input.proof.length = 560 * (input.positions.sort (· ≤ ·)).length +
      32 * ((input.proof.length - 560 * input.positions.card) / 32) := by
    have enough := valid.1
    have whole := valid.2.1
    rw [sorted]
    omega
  have expanded := nonce_expand_records_length (input.positions.sort (· ≤ ·)) input.proof _ size
  rw [sorted] at expanded
  exact expanded

private theorem run_check (program : Submission) (input : CheckInput)
    (admitted : input.proof.length ≤ program.sizes.proof) :
    program.run .check input=execute (program.image .check) (program.steps .check)
      (program.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem nonce_check_valid_exit (input : CheckInput) (valid : NonceCheckValid input) :
    Execution.exit <$> nonceCompressedProgram.run .check input =
      Execution.exit <$> capProgram.run .check (nonceExpandedInput input) := by
  have expandedLength := nonce_expanded_input_length input valid
  have originalAdmitted : input.proof.length ≤ capProgram.sizes.proof := by
    have expandedAdmitted := valid.2.2
    have enough := valid.1
    have whole := valid.2.1
    rw [expandedLength] at expandedAdmitted
    omega
  obtain ⟨next, steps, bound, runs, related⟩ := nonce_expand_valid input valid
  have positive : 0 < capProgram.steps .check := by decide
  rw [run_check nonceCompressedProgram input originalAdmitted]
  erw [nonce_compressed_initial_same .check input]
  change Execution.exit <$> execute nonceExpandedImage (2*capProgram.steps .check)
      (capProgram.initialState .check input) false=_
  have split : 2*capProgram.steps .check =
      steps+(capProgram.steps .check-1+(capProgram.steps .check-steps+1)) := by omega
  rw [split, runs _]
  exact nonce_check_tail_exit (nonceExpandedInput input) valid.2.2 next related _

end CommitGolfCandidate
