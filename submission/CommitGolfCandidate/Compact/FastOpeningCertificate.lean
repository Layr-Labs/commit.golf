import CommitGolfCandidate.Compact.FastOpeningEquivalence
import CommitGolfCandidate.Compact.Machine
import CommitGolfCandidate.Compact.Budgets
import CommitGolfCandidate.Compact.Completeness
import CommitGolfCandidate.Compact.BindingSecurity
import CommitGolfCandidate.Compact.Hiding

/-! The complete certificate concerns fastSubmission and its actual machine runs.
Security transfers through proved equality of the machine-derived schemes; cycle
bounds use the separate complete execution proof of the new opening image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem fast_honest_machine (message : Message) (positions : Positions) :
    fastSubmission.honestMachine message positions=
      (do let committed ← fastSubmission.run .commit message
          let opened ← fastSubmission.run .opening ((fastSubmission.readCommit committed).2,positions)
          return ⟨committed.exit==Exit.success && fastSubmission.openingSucceeded opened,
            committed.cycles,opened.cycles,(fastSubmission.readProof opened).length⟩) := rfl

theorem fast_honest_resources (message : Message) (positions : Positions)
    (result : MachineResult)
    (reached : result∈support (fastSubmission.honestMachine message positions)) :
    result.success=true ∧ result.commitCycles=1728053684 ∧
      result.openingCycles=13+355*positions.card := by
  rw [fast_honest_machine] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,returned⟩ := reached
  rw [fast_opening_execution (fastSubmission.readCommit committed).2 positions] at openReached
  simp only [support_pure,Set.mem_singleton_iff] at openReached returned
  subst opened
  subst result
  have resources := commit_input_resources message committed commitReached
  refine ⟨?_,resources.2.1,rfl⟩
  simp only [resources.1,beq_self_eq_true,Bool.true_and,
    fast_result_succeeded (fastSubmission.readCommit committed).2 positions]

theorem fast_machine_success : fastSubmission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (fast_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

theorem fast_termination : fastSubmission.Termination := by
  intro oracle program input
  cases program with
  | commit => exact submission_termination oracle .commit input
  | check => exact submission_termination oracle .check input
  | opening =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    have executionReached := writer_support (oracle.world.withAddCost Oracle.callCost)
      _ result reached
    have run : fastSubmission.run .opening input=
        pure (fastOpeningResult input.1 input.2) := fast_opening_execution input.1 input.2
    rw [run] at executionReached
    simp only [support_pure,Set.mem_singleton_iff] at executionReached
    rw [executionReached]
    change Exit.success≠Exit.unfinished
    decide

theorem fast_prover_cycles : fastSubmission.ProverCycles 1728053684 45453 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := fast_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1,resources.2.2,batch]
  decide

/-- Every field is checked for the same delivered implementation. -/
theorem fast_certificate : Certificate fastSubmission 101376 1728053684 45453 where
  admission := fast_admission
  machineSuccess := fast_machine_success
  termination := fast_termination
  completeness := by rw [fast_scheme_eq];exact submission_completeness
  honestBudgets := by rw [fast_scheme_eq];exact submission_honest_budgets
  proofSize := by rw [fast_scheme_eq];exact submission_proof_size
  proverCycles := fast_prover_cycles
  binding := by rw [fast_scheme_eq];exact submission_binding
  hidingProperty := by rw [fast_scheme_eq];exact compact_hiding
end CommitGolfCandidate.Compact
