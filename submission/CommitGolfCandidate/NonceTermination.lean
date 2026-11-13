import CommitGolfCandidate.NonceCheckScheme
import CommitGolfCandidate.NonceMachine

/-! All-input termination of each concrete image. A valid packed check has
the same exit computation as the original terminating checker; malformed
proofs reach the actual reject HALT or fail trusted loader admission. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

private theorem oversized_run (program : Submission) (input : CheckInput)
    (oversized : ¬input.proof.length ≤ program.sizes.proof) :
    program.run .check input=pure ⟨.failure,initialMachine,0,0⟩ := by
  simp only [Submission.run,oversized,decide_false,ite_false] <;> rfl

theorem nonce_check_program_terminated (input : CheckInput) (result : Execution)
    (reached : result ∈ support (nonceCompressedProgram.run .check input)) : result.exit ≠ .unfinished := by
  have exitReached : result.exit ∈ support (Execution.exit <$> nonceCompressedProgram.run .check input) := by
    simp only [support_map,Set.mem_image]
    exact ⟨result,reached,rfl⟩
  by_cases valid : NonceCheckValid input
  · have admitted : (nonceExpandedInput input).proof.length ≤ capProgram.sizes.proof := by
      rw [nonce_expanded_input_length input valid.2.1]
      exact valid.2.2
    rw [nonce_check_valid_exit input valid.1 valid.2.1 admitted] at exitReached
    simp only [support_map,Set.mem_image] at exitReached
    obtain ⟨old,oldReached,sameExit⟩:=exitReached
    rw [←sameExit]
    exact cap_check_program_terminated _ old oldReached
  · by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
    · rw [nonce_check_invalid_exit input admitted valid] at exitReached
      simp only [support_pure,Set.mem_singleton_iff] at exitReached
      rw [exitReached]
      decide
    · have oversized : ¬input.proof.length ≤ nonceCompressedProgram.sizes.proof := admitted
      rw [oversized_run nonceCompressedProgram input oversized] at reached
      simp only [support_pure,Set.mem_singleton_iff] at reached
      subst result
      decide

theorem nonce_program_termination : nonceCompressedProgram.Termination := by
  intro oracle phase input
  cases phase with
  | commit => exact submission_termination oracle .commit input
  | opening => exact nonce_opening_program_termination oracle input.1 input.2
  | check =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    exact nonce_check_program_terminated input result.1
      (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
end CommitGolfCandidate
