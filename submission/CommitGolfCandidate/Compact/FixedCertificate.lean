import CommitGolfCandidate.Compact.FixedEquivalence
import CommitGolfCandidate.Compact.Machine
import CommitGolfCandidate.Compact.Budgets
import CommitGolfCandidate.Compact.Completeness
import CommitGolfCandidate.Compact.BindingSecurity
import CommitGolfCandidate.Compact.Hiding

/-! The complete certificate concerns fixedSubmission and its actual machine runs.
Security transfers through proved equality of the machine-derived schemes; cycle
bounds use the separate complete execution proof of the new opening image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem fixed_honest_machine (message : Message) (positions : Positions) :
    fixedSubmission.honestMachine message positions=
      (do let committed ← fixedSubmission.run .commit message
          let opened ← fixedSubmission.run .opening ((fixedSubmission.readCommit committed).2,positions)
          return ⟨committed.exit==Exit.success && fixedSubmission.openingSucceeded opened,
            committed.cycles,opened.cycles,(fixedSubmission.readProof opened).length⟩) := rfl

theorem fixed_honest_resources (message : Message) (positions : Positions)
    (result : MachineResult)
    (reached : result∈support (fixedSubmission.honestMachine message positions)) :
    result.success=true ∧ result.commitCycles=1728053684 ∧
      result.openingCycles=13+306*positions.card := by
  rw [fixed_honest_machine] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,returned⟩ := reached
  rw [fixed_opening_execution (fixedSubmission.readCommit committed).2 positions] at openReached
  simp only [support_pure,Set.mem_singleton_iff] at openReached returned
  subst opened
  subst result
  have resources := commit_input_resources message committed commitReached
  refine ⟨?_,resources.2.1,rfl⟩
  simp only [resources.1,beq_self_eq_true,Bool.true_and,
    fixed_result_succeeded (fixedSubmission.readCommit committed).2 positions]

theorem fixed_machine_success : fixedSubmission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (fixed_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

theorem fixed_termination : fixedSubmission.Termination := by
  intro oracle program input
  cases program with
  | commit => exact submission_termination oracle .commit input
  | check => exact submission_termination oracle .check input
  | opening =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    have executionReached := writer_support (oracle.world.withAddCost Oracle.callCost)
      _ result reached
    have run : fixedSubmission.run .opening input=
        pure (fixedOpeningResult input.1 input.2) := fixed_opening_execution input.1 input.2
    rw [run] at executionReached
    simp only [support_pure,Set.mem_singleton_iff] at executionReached
    rw [executionReached]
    change Exit.success≠Exit.unfinished
    decide

theorem fixed_prover_cycles : fixedSubmission.ProverCycles 1728053684 39181 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := fixed_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1,resources.2.2,batch]
  decide

/-- Every field is checked for the same delivered implementation. -/
theorem fixed_certificate : Certificate fixedSubmission 101376 1728053684 39181 where
  admission := fixed_admission
  machineSuccess := fixed_machine_success
  termination := fixed_termination
  completeness := by rw [fixed_scheme_eq];exact submission_completeness
  honestBudgets := by rw [fixed_scheme_eq];exact submission_honest_budgets
  proofSize := by rw [fixed_scheme_eq];exact submission_proof_size
  proverCycles := fixed_prover_cycles
  binding := by rw [fixed_scheme_eq];exact submission_binding
  hidingProperty := by rw [fixed_scheme_eq];exact compact_hiding
end CommitGolfCandidate.Compact
