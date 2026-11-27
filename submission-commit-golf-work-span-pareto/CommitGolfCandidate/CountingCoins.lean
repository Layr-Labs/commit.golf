import CommitGolfCandidate.Counting

/-! Extend exact public-query accounting to machine runs with private randomness. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem oracle_run_private (oracle : Oracle) (query : unifSpec.Domain) :
    oracle.run (liftM (World.query (.inl query)) : OracleComp World (unifSpec.Range query)) =
      (fun answer => (answer, 0)) <$> (liftM (unifSpec.query query) : ProbComp _) := by
  simp [Oracle.run, Oracle.world, Oracle.callCost, QueryImpl.withAddCost, QueryImpl.withCost]
  rfl

/-- Embedding private randomness in the public-oracle world adds no public calls. -/
theorem oracle_run_coins (oracle : Oracle) {α : Type} (coins : ProbComp α) :
    oracle.run (liftM coins : OracleComp World α) = (fun answer => (answer, 0)) <$> coins := by
  induction coins using OracleComp.inductionOn with
  | pure value => simp [liftM_pure, oracle_run_pure]
  | query_bind query continuation ih =>
    rw [liftM_bind, oracle_run_bind]
    change (do let (answer, first) ← oracle.run (liftM (World.query (.inl query)))
               let (result, second) ← oracle.run (liftM (continuation answer))
               return (result, first + second)) = _
    rw [oracle_run_private]
    simp only [bind_map_left, ih, bind_map_left, Nat.zero_add, map_bind]
    simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- A private random computation followed by a machine continuation leaves the
continuation's independently accumulated public-call count unchanged. -/
theorem oracle_run_coins_bind (oracle : Oracle) {α β : Type} (coins : ProbComp α)
    (continuation : α → OracleComp World β) :
    oracle.run ((liftM coins : OracleComp World α) >>= continuation) =
      (do let answer ← coins
          oracle.run (continuation answer)) := by
  rw [oracle_run_bind, oracle_run_coins]
  simp

/-- Both coin-free and randomized executions report exactly the public calls
counted independently by the security-game oracle runner. -/
theorem execute_counted_with_coins (oracle : Oracle) (image : Image) (steps : Nat)
    (state : MachineState) (allowCoins : Bool) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (execute image steps state allowCoins))) :
    result.1.oracleCalls = result.2 := by
  induction steps generalizing state result with
  | zero =>
    simp only [execute, oracle_run_pure, support_pure, Set.mem_singleton_iff] at reachable
    subst result
    rfl
  | succ steps ih =>
    simp only [execute] at reachable
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
        · split at reachable
          · rw [oracle_run_coins_bind] at reachable
            simp only [mem_support_bind_iff, bind_pure_comp, oracle_run_map,
              support_map, Set.mem_image] at reachable
            obtain ⟨answer, _, previous, before, rfl⟩ := reachable
            simpa only [Execution.charge, Nat.zero_add] using ih _ previous before
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
