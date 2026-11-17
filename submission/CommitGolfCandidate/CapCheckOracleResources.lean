import CommitGolfCandidate.CapCheckTermination
import CommitGolfCandidate.CapCheckEvaluationValue

/-! Lift the actual checker support and structural-query theorems to the
deterministic public handler and the probabilistic certificate runner.
No claimed machine counter substitutes for the handler's counted queries. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_evaluation_bound (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : computation.IsTotalQueryBound budget) :
    (checkEvaluation oracle computation).2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
    rw [check_evaluation_pure]
    exact Nat.zero_le _
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    have cost : (checkEvaluation oracle (liftM (World.query query))).2 ≤ 1 := by
      cases query with
      | inl coins =>
        simp only [checkEvaluation,Oracle.eval,checkHandler,
          QueryImpl.withAddCost,QueryImpl.withCost]
        exact Nat.zero_le _
      | inr queryPublic =>
        rw [check_evaluation_public]
    rw [check_evaluation_bind]
    have tail := ih (checkEvaluation oracle (liftM (World.query query))).1
      (budget-1) (bounded.2 _)
    dsimp only
    omega

theorem cap_check_run_evaluation (oracle : Oracle) (input : CheckInput) :
    oracle.run (capProgram.run .check input) =
      pure (checkEvaluation oracle (capProgram.run .check input)) := by
  by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
  · have execution : capProgram.run .check input =
        execute (capProgram.image .check) (capProgram.steps .check)
          (capProgram.initialState .check input) false := by
      simp only [Submission.run,admitted,decide_true,ite_true]
      rfl
    rw [execution,execute_check_evaluation]
  · simp only [Submission.run,admitted,decide_false,Bool.false_eq_true,ite_false,
      oracle_run_pure,check_evaluation_pure]

theorem cap_check_termination (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$>
      oracle.run (capProgram.run .check input))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  rw [cap_check_run_evaluation] at reached
  simp only [support_pure,Set.mem_singleton_iff] at reached
  subst result
  exact cap_check_program_terminated input
    (checkEvaluation oracle (capProgram.run .check input)).1
    (check_evaluation_support oracle _)

theorem cap_check_scheme_budget (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).2 ≤ 26*input.positions.card := by
  rw [scheme_check_evaluation]
  exact cap_check_evaluation_bound oracle _ _ (cap_check_program_queries input)

end CommitGolfCandidate
