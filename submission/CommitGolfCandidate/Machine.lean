import CommitGolfCandidate.CommitRuntime
import CommitGolfCandidate.CheckInput
import CommitGolfCandidate.OpeningInput

/-! The certificate's machine-success, termination, and prover-cycle requirements.
Cryptographic correctness and security are separate obligations. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Interpreting queries cannot create a result outside the computation's support. -/
theorem writer_support (impl : QueryImpl World (AddWriterT Nat ProbComp))
    {α : Type} (computation : OracleComp World α) (result : α × Multiplicative Nat)
    (reachable : result ∈ support (simulateQ impl computation).run) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at reachable
    subst result
    simp
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
      support_bind, support_map, Set.mem_iUnion, exists_prop, Set.mem_image] at reachable
    obtain ⟨⟨answer, cost⟩, _, ⟨value, extra⟩, reached, rfl⟩ := reachable
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨answer, mem_support_query query answer, ih answer (value, extra) reached⟩

/-- The actual counted oracle runner preserves the commitment's success and cycles,
for every fixed oracle and message. -/
theorem commit_oracle_resources (oracle : Oracle) (message : Message) :
    (prEvent ((fun result => result.1.exit = Exit.success ∧ result.1.cycles = 1811939354) <$> (oracle.run (submission.run .commit message)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := commit_input_resources message result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  exact ⟨resources.1, resources.2.1⟩

/-- All three submitted images terminate on every input, including adversarial
checker inputs. This is the full certificate field, not only a batch test. -/
theorem submission_termination : submission.Termination := by
  intro oracle program input
  cases program with
  | commit =>
    apply (OracleComp.prEvent_eq_one_iff _ _).mpr
    intro result reached
    have resources := commit_input_resources input result.1
      (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
    rw [resources.1]
    decide
  | opening => exact opening_termination oracle input.1 input.2
  | check => exact check_termination oracle input

private theorem honest_machine (candidate : Submission) (message : Message) (positions : Positions) :
    candidate.honestMachine message positions =
      (do let committed ← candidate.run .commit message
          let opened ← candidate.run .opening ((candidate.readCommit committed).2, positions)
          return ⟨committed.exit == Exit.success && candidate.openingSucceeded opened,
            committed.cycles, opened.cycles, (candidate.readProof opened).length⟩) := rfl

/-- Commitment success and opening success concern the same machine-derived scheme,
including the actual private trapdoor returned by commitment. -/
theorem honest_machine_resources (message : Message) (positions : Positions)
    (result : MachineResult) (reachable : result ∈ support (submission.honestMachine message positions)) :
    result.success = true ∧ result.commitCycles = 1811939354 ∧
      result.openingCycles = 24 + 380 * positions.card := by
  rw [honest_machine] at reachable
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨committed, committedReached, opened, openedReached, returned⟩ := reachable
  rw [opening_execution] at openedReached
  simp only [support_pure, Set.mem_singleton_iff] at openedReached returned
  subst opened
  subst result
  have committedResources := commit_input_resources message committed committedReached
  refine ⟨?_, committedResources.2.1, rfl⟩
  simp only [committedResources.1, beq_self_eq_true, Bool.true_and, opening_result_succeeded]

/-- Both honest machine runs succeed with probability one for every message and
opening set. This proves the certificate's machine-success field. -/
theorem submission_machine_success : submission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

/-- Certified upper bounds from the actual images for a complete commitment and a
128-leaf opening. These are the declared claim values, not a sampled measurement. -/
theorem submission_prover_cycles : submission.ProverCycles 1811939354 48664 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have resources := honest_machine_resources message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)
  rw [resources.2.1, resources.2.2, batch]
  decide

end CommitGolfCandidate
