import CommitGolfCandidate.NonceCheckGuards

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private theorem scheme_check_exit (program : Submission) (input : CheckInput) :
    program.scheme.check input.commitment input.positions input.values input.proof=
      (fun exit => exit==Exit.success) <$>
        simulateQ checkHandler (Execution.exit <$> program.run .check input) := by
  simp only [simulateQ_map,Functor.map_map,Function.comp_def]
  rfl

theorem nonce_check_scheme_valid (input : CheckInput) (valid : NonceCheckValid input) :
    nonceCompressedProgram.scheme.check input.commitment input.positions input.values input.proof=
      capProgram.scheme.check input.commitment input.positions input.values (nonceExpandedInput input).proof := by
  have admitted : (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof := by
    rw [nonce_expanded_input_length input valid.2.1]
    exact valid.2.2
  rw [scheme_check_exit nonceCompressedProgram input,
    nonce_check_valid_exit input valid.1 valid.2.1 admitted]
  exact (scheme_check_exit capProgram (nonceExpandedInput input)).symm

theorem nonce_check_scheme_invalid (input : CheckInput) (invalid : ¬NonceCheckValid input) :
    nonceCompressedProgram.scheme.check input.commitment input.positions input.values input.proof=pure false := by
  by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
  · rw [scheme_check_exit nonceCompressedProgram input,nonce_check_invalid_exit input admitted invalid]
    rfl
  · have rejected : nonceCompressedProgram.run .check input=pure ⟨.failure,initialMachine,0,0⟩ := by
      have oversized : ¬input.proof.length ≤ nonceCompressedProgram.sizes.proof := admitted
      simp only [Submission.run,oversized,decide_false,ite_false] <;> rfl
    rw [scheme_check_exit nonceCompressedProgram input,rejected]
    rfl

theorem nonce_check_acceptance_expand (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (nonceCompressedProgram.scheme.check input.commitment input.positions input.values input.proof)).1=true) :
    (oracle.eval (capProgram.scheme.check input.commitment input.positions input.values (nonceExpandedInput input).proof)).1=true := by
  by_cases valid : NonceCheckValid input
  · rw [nonce_check_scheme_valid input valid] at accepted
    exact accepted
  · rw [nonce_check_scheme_invalid input valid] at accepted
    simp only [Oracle.eval,simulateQ_pure,WriterT.run_pure] at accepted
    contradiction
end CommitGolfCandidate
