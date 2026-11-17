import CommitGolfCandidate.Compact.SlimEquivalence
import CommitGolfCandidate.Compact.Machine
import CommitGolfCandidate.Compact.Budgets
import CommitGolfCandidate.Compact.Completeness
import CommitGolfCandidate.Compact.BindingSecurity
import CommitGolfCandidate.Compact.Hiding

/-! The complete certificate concerns slimSubmission and its actual machine runs.
Security transfers through proved equality of the machine-derived schemes; cycle
bounds use the separate complete execution proof of the new opening image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem slim_honest_machine (message : Message) (positions : Positions) :
    slimSubmission.honestMachine message positions=
      (do let committed ← slimSubmission.run .commit message
          let opened ← slimSubmission.run .opening ((slimSubmission.readCommit committed).2,positions)
          return ⟨committed.exit==Exit.success && slimSubmission.openingSucceeded opened,
            committed.cycles,opened.cycles,(slimSubmission.readProof opened).length⟩) := rfl

theorem slim_honest_resources (message : Message) (positions : Positions)
    (result : MachineResult)
    (reached : result∈support (slimSubmission.honestMachine message positions)) :
    result.success=true ∧ result.commitCycles=1728053684 ∧
      result.openingCycles=13+332*positions.card := by
  rw [slim_honest_machine] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,returned⟩ := reached
  rw [slim_opening_execution (slimSubmission.readCommit committed).2 positions] at openReached
  simp only [support_pure,Set.mem_singleton_iff] at openReached returned
  subst opened
  subst result
  have resources := commit_input_resources message committed commitReached
  refine ⟨?_,resources.2.1,rfl⟩
  simp only [resources.1,beq_self_eq_true,Bool.true_and,
    slim_result_succeeded (slimSubmission.readCommit committed).2 positions]

theorem slim_machine_success : slimSubmission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (slim_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

theorem slim_termination : slimSubmission.Termination := by
  intro oracle program input
  cases program with
  | commit => exact submission_termination oracle .commit input
  | check => exact submission_termination oracle .check input
  | opening =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    have executionReached := writer_support (oracle.world.withAddCost Oracle.callCost)
      _ result reached
    have run : slimSubmission.run .opening input=
        pure (slimOpeningResult input.1 input.2) := slim_opening_execution input.1 input.2
    rw [run] at executionReached
    simp only [support_pure,Set.mem_singleton_iff] at executionReached
    rw [executionReached]
    change Exit.success≠Exit.unfinished
    decide

theorem slim_prover_cycles : slimSubmission.ProverCycles 1728053684 42509 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := slim_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1,resources.2.2,batch]
  decide

/-- Every field is checked for the same delivered implementation. -/
theorem slim_certificate : Certificate slimSubmission 101376 1728053684 42509 where
  admission := slim_admission
  machineSuccess := slim_machine_success
  termination := slim_termination
  completeness := by rw [slim_scheme_eq];exact submission_completeness
  honestBudgets := by rw [slim_scheme_eq];exact submission_honest_budgets
  proofSize := by rw [slim_scheme_eq];exact submission_proof_size
  proverCycles := slim_prover_cycles
  binding := by rw [slim_scheme_eq];exact submission_binding
  hidingProperty := by rw [slim_scheme_eq];exact compact_hiding
end CommitGolfCandidate.Compact
