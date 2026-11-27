import CommitGolfDepth.Rounds.Legacy

/-! # Proving bootstrap round bounds from actual legacy executions

These support lemmas concern the execution's oracle-call field, not a claimed
query count. They let existing machine-resource theorems supply exact round bounds
without assuming that a new batched interpreter is compatible with old code.
-/

namespace CommitGolfDepth.Rounds

open CommitGolf CommitGolf.Riscv OracleComp OracleSpec

/-- Artifact equality includes both the delivered core and every phase's mode. -/
@[ext] theorem Submission.ext {left right : Submission}
    (core : left.core = right.core) (modes : left.modes = right.modes) : left = right := by
  cases left
  cases right
  cases core
  cases modes
  rfl

/-- A handler may restrict replies, but cannot create a new syntactic result. -/
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

/-- Exact old-program call bounds become almost-sure new rounds bounds in legacy mode. -/
theorem legacyRoundBounds_of_support (core : CommitGolf.Submission)
    (commitRounds openingRounds : Nat)
    (commitBound : ∀ (message : Message) (result : Riscv.Execution),
      result ∈ support (core.run .commit message) → result.oracleCalls ≤ commitRounds)
    (openingBound : ∀ (trapdoor : BitVec (8 * core.sizes.trapdoor)) (positions : Positions),
      positions.card = BATCH → ∀ (result : Riscv.Execution),
        result ∈ support (core.run .opening (trapdoor, positions)) →
          result.oracleCalls ≤ openingRounds) :
    (Submission.ofLegacy core).RoundBounds commitRounds openingRounds := by
  intro oracle message positions cardinality
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have possible := writer_support (oracle.world.withAddCost Oracle.callCost)
    ((Submission.ofLegacy core).honestMachine message positions) result reached
  rw [Submission.honestMachine, run_ofLegacy core .commit message, bind_map_left] at possible
  obtain ⟨committed, committedReachable, rest⟩ := (mem_support_bind_iff _ _ _).mp possible
  dsimp only [Submission.ofLegacy, liftLegacy, CommitGolf.Submission.readCommit] at rest
  let openingInput : Input core.sizes .opening :=
    (readBuffer committed.state core.layout.trapdoor core.sizes.trapdoor, positions)
  change result.1 ∈ support (do
    let opened ← (Submission.ofLegacy core).run .opening openingInput
    return ({
      success := committed.exit == Riscv.Exit.success && core.openingSucceeded opened.result
      commitCycles := committed.cycles
      openingCycles := opened.result.cycles
      proofBytes := (core.readProof opened.result).length
      commitRounds := committed.oracleCalls
      openingRounds := opened.oracleRounds } : MachineResult)) at rest
  rw [run_ofLegacy core .opening openingInput, bind_map_left] at rest
  obtain ⟨opened, openedReachable, final⟩ := (mem_support_bind_iff _ _ _).mp rest
  simp only [support_pure, Set.mem_singleton_iff] at final
  rw [final]
  exact ⟨commitBound message committed committedReachable,
    openingBound _ positions cardinality opened openedReachable⟩

end CommitGolfDepth.Rounds
