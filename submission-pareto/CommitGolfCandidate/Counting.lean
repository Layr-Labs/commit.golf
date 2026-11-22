import CommitGolfCandidate.Execution

/-! Relate the interpreter's public-call counter to the security game's counter.
The latter is maintained independently by the oracle runner. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

theorem oracle_run_bind (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    oracle.run (computation >>= continuation) =
      (do let (value, first) ← oracle.run computation
          let (result, second) ← oracle.run (continuation value)
          return (result, first + second)) := by
  simp only [Oracle.run, simulateQ_bind, WriterT.run_bind, map_eq_bind_pure_comp]
  rfl

theorem oracle_run_public (oracle : Oracle) (query : PublicSpec.Domain) :
    oracle.run (liftM (World.query (.inr query)) : OracleComp World (PublicSpec.Range query)) =
      pure (oracle.answer (m := Id) query, 1) := by
  rcases query with input | input
  · simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
      QueryImpl.withAddCost, QueryImpl.withCost]
    rfl
  · rcases input with input | input <;>
      simp [Oracle.run, Oracle.world, Oracle.answer, Oracle.callCost,
        QueryImpl.withAddCost, QueryImpl.withCost] <;> rfl

/-- Ordinary result mapping changes neither the runner's query count nor its coins. -/
theorem oracle_run_map (oracle : Oracle) {α β : Type} (f : α → β)
    (computation : OracleComp World α) :
    oracle.run (f <$> computation) = (fun result => (f result.1, result.2)) <$> oracle.run computation := by
  rw [map_eq_bind_pure_comp, oracle_run_bind]
  simp only [Function.comp_apply, oracle_run_pure, pure_bind, Nat.add_zero]
  simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Every counted result of a mapped computation comes from a counted result of the computation.

Proofs about the submitted machine use this lemma and the other support lemmas stated for an
abstract computation, instead of rewriting their hypotheses. Since `Set` became a structure
(Mathlib #41506), Lean's kernel can reduce both sides of a comparison `x ∈ support a =?= x ∈ support b`
when `a` and `b` differ syntactically, and this reduction runs the computations. For the commitment
run, it evaluates `2 ^ width` for the 2^32-bit salt, which the kernel refuses. Applied to the actual
run, the hypothesis of such a lemma matches the caller's hypothesis syntactically. -/
theorem oracle_run_map_support (oracle : Oracle) {α β : Type} (f : α → β)
    (computation : OracleComp World α) (result : β × Nat)
    (reachable : result ∈ support (oracle.run (f <$> computation))) :
    ∃ counted ∈ support (oracle.run computation), result = (f counted.1, counted.2) := by
  rw [oracle_run_map] at reachable
  simp only [support_map, Set.mem_image] at reachable
  obtain ⟨counted, reached, rfl⟩ := reachable
  exact ⟨counted, reached, rfl⟩

/-- A public query contributes exactly one call before continuing. -/
theorem oracle_run_public_bind (oracle : Oracle) {α : Type} (query : PublicSpec.Domain)
    (continuation : PublicSpec.Range query → OracleComp World α) :
    oracle.run ((liftM (World.query (.inr query)) : OracleComp World _) >>= continuation) =
      (do let (result, calls) ← oracle.run (continuation (oracle.answer (m := Id) query))
          return (result, 1 + calls)) := by
  rw [oracle_run_bind, oracle_run_public]
  simp

/-- For coin-free execution, the interpreter's call counter agrees with the
security game's independent writer counter, on every possible run. -/
theorem execute_counted (oracle : Oracle) (image : Image) (steps : Nat) (state : MachineState)
    (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (execute image steps state false))) :
    result.1.oracleCalls = result.2 := by
  induction steps generalizing state result with
  | zero =>
    simp only [execute, oracle_run_pure, support_pure, Set.mem_singleton_iff] at reachable
    subst result
    rfl
  | succ steps ih =>
    simp only [execute, Bool.false_and, Bool.false_eq_true, ite_false] at reachable
    split at reachable
    · rw [oracle_run_pure] at reachable
      simp only [support_pure, Set.mem_singleton_iff] at reachable
      subst result
      rfl
    · split at reachable
      · split at reachable
        · rw [oracle_run_pure] at reachable
          simp only [support_pure, Set.mem_singleton_iff] at reachable
          subst result
          rfl
        · rw [oracle_run_public_bind] at reachable
          simp only [bind_pure_comp, oracle_run_map, support_map, Set.mem_image] at reachable
          obtain ⟨_, ⟨previous, before, rfl⟩, rfl⟩ := reachable
          have counted := ih _ previous before
          simp only [Execution.charge]
          omega
      · split at reachable
        · rw [oracle_run_pure] at reachable
          simp only [support_pure, Set.mem_singleton_iff] at reachable
          subst result
          rfl
        · rw [oracle_run_pure] at reachable
          simp only [support_pure, Set.mem_singleton_iff] at reachable
          subst result
          rfl
    · split at reachable
      · rw [oracle_run_pure] at reachable
        simp only [support_pure, Set.mem_singleton_iff] at reachable
        subst result
        rfl
      · simp only [bind_pure_comp, oracle_run_map, support_map, Set.mem_image] at reachable
        obtain ⟨previous, before, rfl⟩ := reachable
        simpa only [Execution.charge, Nat.zero_add] using ih _ previous before

end CommitGolfCandidate
