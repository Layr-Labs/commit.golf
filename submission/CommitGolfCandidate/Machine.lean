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

/-- A property that holds for every counted result whose execution is in the support of `run`
holds with probability one for the counted oracle runner.

The statement keeps `run` abstract. Applied to a concrete machine run, its hypothesis and
conclusion then match the goal syntactically. Since `Set` became a structure (Mathlib #41506),
Lean's kernel reduces both sides of a comparison `x ∈ support a =?= x ∈ support b` when `a` and `b`
differ syntactically. For the commitment run, that reduction evaluates `2 ^ width` for the
2^32-bit salt, which the kernel refuses. -/
private theorem counted_of_each {α : Type} (oracle : Oracle) (run : OracleComp World α)
    (property : α × Nat → Prop)
    (each : ∀ result : α × Nat, result.1 ∈ support run → property result) :
    Pr{let result ← oracle.run run}[property result] = 1 :=
  (OracleComp.prEvent_eq_one_iff _ _).mpr fun result reached =>
    each result (writer_support (oracle.world.withAddCost Oracle.callCost) run result reached)

/-- The actual counted oracle runner preserves the commitment's success and cycles,
for every fixed oracle and message. -/
theorem commit_oracle_resources (oracle : Oracle) (message : Message) :
    (prEvent ((fun result => result.1.exit = Exit.success ∧ result.1.cycles = 3959423012) <$> (oracle.run (submission.run .commit message)))) = 1 :=
  counted_of_each oracle (submission.run .commit message)
    (fun result => result.1.exit = Exit.success ∧ result.1.cycles = 3959423012)
    fun result reached =>
      ⟨(commit_input_resources message result.1 reached).1,
        (commit_input_resources message result.1 reached).2.1⟩

/-- All three submitted images terminate on every input, including adversarial
checker inputs. This is the full certificate field, not only a batch test. -/
theorem submission_termination : submission.Termination := by
  intro oracle program input
  cases program with
  | commit =>
    refine counted_of_each oracle (submission.run .commit input)
      (fun result => result.1.exit ≠ Riscv.Exit.unfinished) fun result reached => ?_
    rw [(commit_input_resources input result.1 reached).1]
    decide
  | opening => exact opening_termination oracle input.1 input.2
  | check => exact check_termination oracle input

private theorem honest_machine (candidate : Submission) (message : Message) (positions : Positions) :
    candidate.honestMachine message positions =
      (do let committed ← candidate.run .commit message
          let opened ← candidate.run .opening ((candidate.readCommit committed).2, positions)
          return ⟨committed.exit == Exit.success && candidate.openingSucceeded opened,
            committed.cycles, opened.cycles, (candidate.readProof opened).length⟩) := rfl

/-- `honest_machine_resources` for an abstract commitment run `commit` whose outcomes all
succeed with the commitment's cycle count. Keeping `commit` abstract keeps the kernel from
reducing the actual commitment run; see `counted_of_each`. -/
private theorem honest_resources_of (positions : Positions)
    (commit : OracleComp World Execution)
    (committed : ∀ execution ∈ support commit,
      execution.exit = Exit.success ∧ execution.cycles = 3959423012)
    (result : MachineResult)
    (reachable : result ∈ support (do
      let committed ← commit
      let opened ← submission.run .opening ((submission.readCommit committed).2, positions)
      return (⟨committed.exit == Exit.success && submission.openingSucceeded opened,
        committed.cycles, opened.cycles, (submission.readProof opened).length⟩ :
          MachineResult))) :
    result.success = true ∧ result.commitCycles = 3959423012 ∧
      result.openingCycles = 30 + 380 * positions.card := by
  simp only [mem_support_bind_iff] at reachable
  obtain ⟨execution, executionReached, opened, openedReached, returned⟩ := reachable
  rw [opening_execution] at openedReached
  simp only [support_pure, Set.mem_singleton_iff] at openedReached returned
  subst opened
  subst result
  have committedResources := committed execution executionReached
  refine ⟨?_, committedResources.2, rfl⟩
  simp only [committedResources.1, beq_self_eq_true, Bool.true_and, opening_result_succeeded]

/-- Commitment success and opening success concern the same machine-derived scheme,
including the actual private trapdoor returned by commitment. -/
theorem honest_machine_resources (message : Message) (positions : Positions)
    (result : MachineResult) (reachable : result ∈ support (submission.honestMachine message positions)) :
    result.success = true ∧ result.commitCycles = 3959423012 ∧
      result.openingCycles = 30 + 380 * positions.card := by
  rw [honest_machine] at reachable
  generalize commitRun : submission.run .commit message = commit at reachable
  refine honest_resources_of positions commit (fun execution reached => ?_) result reachable
  rw [← commitRun] at reached
  exact ⟨(commit_input_resources message execution reached).1,
    (commit_input_resources message execution reached).2.1⟩

/-- Both honest machine runs succeed with probability one for every message and
opening set. This proves the certificate's machine-success field. -/
theorem submission_machine_success : submission.MachineSuccess := by
  intro oracle message positions
  exact counted_of_each oracle (submission.honestMachine message positions)
    (fun result => result.1.success = true) fun result reached =>
      (honest_machine_resources message positions result.1 reached).1

/-- Certified upper bounds from the actual images for a complete commitment and a
128-leaf opening. These are the declared claim values, not a sampled measurement. -/
theorem submission_prover_cycles : submission.ProverCycles 3959423012 48670 := by
  intro oracle message positions batch
  refine counted_of_each oracle (submission.honestMachine message positions)
    (fun result => result.1.commitCycles ≤ 3959423012 ∧ result.1.openingCycles ≤ 48670)
    fun result reached => ?_
  have resources := honest_machine_resources message positions result.1 reached
  rw [resources.2.1, resources.2.2, batch]
  decide

end CommitGolfCandidate
