import CommitGolfCandidate.CheckInput

/-! Connect deterministic checker evaluation to the counted security-game runner. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- Evaluate a world computation with check's public-only handler. Coin queries
would be replaced by zero, but the checker interpreter never makes any. -/
def checkEvaluation (oracle : Oracle) {α : Type} (computation : OracleComp World α) : α × Nat :=
  oracle.eval (simulateQ checkHandler computation)

theorem check_evaluation_pure (oracle : Oracle) {α : Type} (value : α) :
    checkEvaluation oracle (pure value) = (value, 0) := by
  simp [checkEvaluation, Oracle.eval]
  rfl

theorem check_evaluation_bind (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    checkEvaluation oracle (computation >>= continuation) =
      let (value, first) := checkEvaluation oracle computation
      let (result, second) := checkEvaluation oracle (continuation value)
      (result, first + second) := by
  simp only [checkEvaluation, Oracle.eval, simulateQ_bind, WriterT.run_bind]
  rfl

theorem check_evaluation_map (oracle : Oracle) {α β : Type} (f : α → β)
    (computation : OracleComp World α) :
    checkEvaluation oracle (f <$> computation) =
      (f (checkEvaluation oracle computation).1, (checkEvaluation oracle computation).2) := by
  rw [map_eq_bind_pure_comp, check_evaluation_bind]
  simp [check_evaluation_pure]

theorem check_evaluation_public (oracle : Oracle) (query : PublicSpec.Domain) :
    checkEvaluation oracle (liftM (World.query (.inr query)) : OracleComp World (PublicSpec.Range query)) =
      (oracle.answer (m := Id) query, 1) := by
  simp [checkEvaluation, Oracle.eval, checkHandler, QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

theorem check_evaluation_public_bind (oracle : Oracle) {α : Type} (query : PublicSpec.Domain)
    (continuation : PublicSpec.Range query → OracleComp World α) :
    checkEvaluation oracle ((liftM (World.query (.inr query)) : OracleComp World _) >>= continuation) =
      let (result, calls) := checkEvaluation oracle (continuation (oracle.answer (m := Id) query))
      (result, 1 + calls) := by
  rw [check_evaluation_bind, check_evaluation_public]

/-- Deterministic evaluation selects an actual supported computation result.
This lets the machine's reply-independent invariants apply to a fixed oracle. -/
theorem check_evaluation_support (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) :
    (checkEvaluation oracle computation).1 ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [check_evaluation_pure]
  | query_bind query continuation ih =>
    rw [check_evaluation_bind]
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨(checkEvaluation oracle (liftM (World.query query))).1, mem_support_query query _, ih _⟩

/-- Coin-free execution has the same result and cost under both interpreters. -/
theorem execute_check_evaluation (oracle : Oracle) (image : Image) (steps : Nat) (state : MachineState) :
    oracle.run (execute image steps state false) =
      pure (checkEvaluation oracle (execute image steps state false)) := by
  induction steps generalizing state with
  | zero => simp only [execute, oracle_run_pure, check_evaluation_pure]
  | succ steps ih =>
    simp only [execute, Bool.false_and, Bool.false_eq_true, ite_false]
    split
    · rw [oracle_run_pure, check_evaluation_pure]
    · split
      · split
        · rw [oracle_run_pure, check_evaluation_pure]
        · rw [oracle_run_public_bind, check_evaluation_public_bind]
          simp only [bind_pure_comp, oracle_run_map, check_evaluation_map, ih, map_pure]
      · split <;> rw [oracle_run_pure, check_evaluation_pure]
    · split
      · rw [oracle_run_pure, check_evaluation_pure]
      · simp only [bind_pure_comp, oracle_run_map, check_evaluation_map, ih, map_pure]

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

/-- The deterministic check count used by the honest security game obeys the
interpreter proof for every proof, commitment, value vector, and index set. -/
theorem scheme_check_budget (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      32 * input.positions.card := by
  rw [scheme_check_evaluation]
  have reached : checkEvaluation oracle (submission.run .check input) ∈
      support (oracle.run (submission.run .check input)) := by
    rw [check_run_evaluation]
    simp
  have event := ((OracleComp.prEvent_eq_one_iff _ _).mp (check_oracle_resources oracle input)) _ reached
  exact event.2.2

end CommitGolfCandidate
