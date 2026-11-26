import CommitGolfCandidate.TruncDistribution
import CommitGolfCandidate.TruncResources
import CommitGolfCandidate.Budgets
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 180000
attribute [local irreducible] commitSaltCoins commitFinalResult
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

/-- Each honest commitment makes exactly 5*N-1 public queries, including every
underlying compression call in the four-block salted leaf construction. -/
theorem scheme_commit_calls (oracle : Oracle) (message : Message)
    (result : (Commitment × submission.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (submission.scheme.commit message))) :
    result.2 = 83886079 := by
  rw [scheme_commit] at reachable
  change result ∈ support (oracle.run (submission.readCommit <$>
    submission.run .commit (message : Input submission.sizes .commit))) at reachable
  rw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨committed, reached, rfl⟩ := reachable
  change committed.2 = 83886079
  rw [← commit_counted oracle message committed reached]
  exact (commit_input_resources message committed.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ committed reached)).2.2


theorem committedOrigin (o : Oracle) (m : Message) (z : Execution × Nat) (h : z∈support (o.run (submission.run .commit m))) :
    CommittedState o m z.1.state := by
  have hit := (congrArg (fun p : ProbComp (Execution×Nat)=>z∈support p) (commit_run_distribution o m)).mp h
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨a,_,rfl⟩:=hit
  exact (commit_final_origin o m a (CommitGolfCandidate.commit_salt_width m)).1
end CommitGolfCandidate.Trunc
