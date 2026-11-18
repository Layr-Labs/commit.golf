import CommitGolfCandidate.NonceCheckValidExit
import CommitGolfCandidate.NonceCheckExit

/-! The delivered checker rejects every admitted proof that does not expand: the expansion
reaches the retained reject HALT before reading a proof word or making an oracle query. A proof
that `s6Expand` accepts, with an expansion inside the capacity, is one the checker expands. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 700000

theorem nonce_check_valid_of_expand (input : CheckInput) (expanded : List Byte)
    (expand : s6Expand input.positions input.proof = some expanded)
    (admitted : expanded.length ≤ capProgram.sizes.proof) :
    NonceCheckValid input ∧ (nonceExpandedInput input).proof = expanded := by
  unfold s6Expand at expand
  split at expand
  · rename_i shape
    have same : (nonceExpandedInput input).proof = expanded := Option.some.inj expand
    refine ⟨⟨shape.1, shape.2, ?_⟩, same⟩
    rw [same]
    exact admitted
  · contradiction

private theorem run_check (program : Submission) (input : CheckInput)
    (admitted : input.proof.length ≤ program.sizes.proof) :
    program.run .check input=execute (program.image .check) (program.steps .check)
      (program.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem nonce_check_invalid_exit (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) (invalid : ¬NonceCheckValid input) :
    Execution.exit <$> nonceCompressedProgram.run .check input=pure .failure := by
  obtain ⟨next, steps, bound, runs, pc⟩ := nonce_expand_invalid input admitted invalid
  have large : 27 ≤ capProgram.steps .check := by decide
  rw [run_check nonceCompressedProgram input admitted]
  erw [nonce_compressed_initial_same .check input]
  change Execution.exit <$> execute nonceExpandedImage (2*capProgram.steps .check)
    (capProgram.initialState .check input) false=_
  have split : 2*capProgram.steps .check = steps+(3+(2*capProgram.steps .check-steps-3)) := by omega
  have halt := nonce_expanded_check_exit next false (pc.trans rfl) (2*capProgram.steps .check-steps-3) false
  rw [split, runs _, halt]
  rfl

end CommitGolfCandidate
