import CommitGolfCandidate.Machine
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.CheckEvaluation

/-! Honest public-query budgets for the scheme defined by the submitted images. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem run_commit (candidate : Submission) (message : Message) :
    candidate.run .commit message = execute (candidate.image .commit) (candidate.steps .commit)
      (candidate.initialState .commit message) true := rfl

/-- Private salt sampling does not disturb equality of the two query counters. -/
theorem commit_counted (oracle : Oracle) (message : Message) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .commit message))) :
    result.1.oracleCalls = result.2 := by
  rw [run_commit] at reachable
  exact execute_counted_with_coins oracle _ _ _ true result reachable

private theorem scheme_commit (candidate : Submission) (message : Message) :
    candidate.scheme.commit message = candidate.readCommit <$> candidate.run .commit message := rfl

/-- Each honest commitment makes exactly 3*N-1 public queries: two permutation
calls per leaf digest and one compression call per internal node. -/
theorem scheme_commit_calls (oracle : Oracle) (message : Message)
    (result : (Commitment × submission.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (submission.scheme.commit message))) :
    result.2 = 50331647 := by
  rw [scheme_commit] at reachable
  change result ∈ support (oracle.run (submission.readCommit <$>
    submission.run .commit (message : Input submission.sizes .commit))) at reachable
  rw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨committed, reached, rfl⟩ := reachable
  change committed.2 = 50331647
  rw [← commit_counted oracle message committed reached]
  exact (commit_input_resources message committed.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ committed reached)).2.2

/-- The complete honest-budget certificate field, for every fixed oracle, message,
and set of opened positions. Commitment uses 3*N-1 calls, opening uses zero, and
checking uses at most 32 calls per opened leaf. -/
theorem submission_honest_budgets : submission.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, commitCalls⟩, committed, rest⟩ := reached
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure] at rest
  simp only [support_pure, Set.mem_singleton_iff] at rest
  obtain ⟨opened, rfl, rfl⟩ := rest
  have commitment := scheme_commit_calls oracle message ((root, trapdoor), commitCalls) committed
  have checker := scheme_check_budget oracle
    ⟨root, positions, message.restrict positions, submission.readProof (openingResult trapdoor positions)⟩
  dsimp only at commitment checker
  refine ⟨?_, ?_, ?_⟩
  · change commitCalls ≤ COMMIT_BUDGET
    rw [commitment]
    decide
  · change 0 ≤ OPEN_BUDGET positions.card
    exact Nat.zero_le _
  · change (oracle.eval (submission.scheme.check root positions (message.restrict positions)
      (submission.readProof (openingResult trapdoor positions)))).2 ≤ CHECK_BUDGET positions.card
    exact checker.trans (by unfold CHECK_BUDGET; omega)

end CommitGolfCandidate
