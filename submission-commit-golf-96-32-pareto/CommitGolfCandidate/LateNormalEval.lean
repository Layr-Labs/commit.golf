import CommitGolfCandidate.LateNormalImage

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

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

theorem check_evaluation_support (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) :
    (checkEvaluation oracle computation).1 ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [check_evaluation_pure]
  | query_bind query continuation ih =>
    rw [check_evaluation_bind]
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨(checkEvaluation oracle (liftM (World.query query))).1, mem_support_query query _, ih _⟩

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

theorem scheme_check_evaluation (oracle : Oracle) (candidate : Submission) (input : CheckInput) :
    oracle.eval (candidate.scheme.check input.commitment input.positions input.values input.proof) =
      ((checkEvaluation oracle (candidate.run .check input)).1.exit == Exit.success,
        (checkEvaluation oracle (candidate.run .check input)).2) := by
  simp only [Submission.scheme, Oracle.eval, simulateQ_map, WriterT.run_map]
  rfl

end CommitGolfCandidate.Late.Check.Normal
