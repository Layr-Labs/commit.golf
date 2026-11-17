import CommitGolfCandidate.Compact.NoJumpEquivalence
import CommitGolfCandidate.Compact.Machine
import CommitGolfCandidate.Compact.Budgets
import CommitGolfCandidate.Compact.Completeness
import CommitGolfCandidate.Compact.BindingSecurity
import CommitGolfCandidate.Compact.Hiding

/-! The complete certificate concerns noJumpSubmission and its actual machine runs.
Security transfers through proved equality of the machine-derived schemes; cycle
bounds use the separate complete execution proof of the new opening image. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem noJump_honest_machine (message : Message) (positions : Positions) :
    noJumpSubmission.honestMachine message positions=
      (do let committed ← noJumpSubmission.run .commit message
          let opened ← noJumpSubmission.run .opening ((noJumpSubmission.readCommit committed).2,positions)
          return ⟨committed.exit==Exit.success && noJumpSubmission.openingSucceeded opened,
            committed.cycles,opened.cycles,(noJumpSubmission.readProof opened).length⟩) := rfl

theorem noJump_honest_resources (message : Message) (positions : Positions)
    (result : MachineResult)
    (reached : result∈support (noJumpSubmission.honestMachine message positions)) :
    result.success=true ∧ result.commitCycles=1728053684 ∧
      result.openingCycles=13+329*positions.card := by
  rw [noJump_honest_machine] at reached
  simp only [mem_support_bind_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,returned⟩ := reached
  rw [noJump_opening_execution (noJumpSubmission.readCommit committed).2 positions] at openReached
  simp only [support_pure,Set.mem_singleton_iff] at openReached returned
  subst opened
  subst result
  have resources := commit_input_resources message committed commitReached
  refine ⟨?_,resources.2.1,rfl⟩
  simp only [resources.1,beq_self_eq_true,Bool.true_and,
    noJump_result_succeeded (noJumpSubmission.readCommit committed).2 positions]

theorem noJump_machine_success : noJumpSubmission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (noJump_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

theorem noJump_termination : noJumpSubmission.Termination := by
  intro oracle program input
  cases program with
  | commit => exact submission_termination oracle .commit input
  | check => exact submission_termination oracle .check input
  | opening =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    have executionReached := writer_support (oracle.world.withAddCost Oracle.callCost)
      _ result reached
    have run : noJumpSubmission.run .opening input=
        pure (noJumpOpeningResult input.1 input.2) := noJump_opening_execution input.1 input.2
    rw [run] at executionReached
    simp only [support_pure,Set.mem_singleton_iff] at executionReached
    rw [executionReached]
    change Exit.success≠Exit.unfinished
    decide

theorem noJump_prover_cycles : noJumpSubmission.ProverCycles 1728053684 42125 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := noJump_honest_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1,resources.2.2,batch]
  decide

/-- Every field is checked for the same delivered implementation. -/
theorem noJump_certificate : Certificate noJumpSubmission 101376 1728053684 42125 where
  admission := noJump_admission
  machineSuccess := noJump_machine_success
  termination := noJump_termination
  completeness := by rw [noJump_scheme_eq];exact submission_completeness
  honestBudgets := by rw [noJump_scheme_eq];exact submission_honest_budgets
  proofSize := by rw [noJump_scheme_eq];exact submission_proof_size
  proverCycles := noJump_prover_cycles
  binding := by rw [noJump_scheme_eq];exact submission_binding
  hidingProperty := by rw [noJump_scheme_eq];exact compact_hiding
end CommitGolfCandidate.Compact
