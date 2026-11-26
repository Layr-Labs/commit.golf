import CommitGolfCandidate.CheckAcceptance

/-! Connect deterministic checker evaluation to the counted security-game runner. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem run_check (candidate : Submission) (input : CheckInput)
    (valid : input.proof.length ≤ candidate.sizes.proof) :
    candidate.run .check input = execute (candidate.image .check) (candidate.steps .check)
      (candidate.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]
  rfl

/-- The trusted check ABI preserves that equality, including rejection of oversized proofs. -/
theorem check_run_evaluation (oracle : Oracle) (input : CheckInput) :
    oracle.run (submission.run .check input) =
      pure (checkEvaluation oracle (submission.run .check input)) := by
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · rw [run_check submission input valid, execute_check_evaluation]
  · rw [check_oversized input (by omega), oracle_run_pure, check_evaluation_pure]

/-- The scheme's check result and call count are the machine evaluation, with only
its exit code mapped to acceptance. -/
theorem scheme_check_evaluation (oracle : Oracle) (candidate : Submission) (input : CheckInput) :
    oracle.eval (candidate.scheme.check input.commitment input.positions input.values input.proof) =
      ((checkEvaluation oracle (candidate.run .check input)).1.exit == Exit.success,
        (checkEvaluation oracle (candidate.run .check input)).2) := by
  simp only [Submission.scheme, Oracle.eval, simulateQ_map, WriterT.run_map]
  rfl

end CommitGolfCandidate
