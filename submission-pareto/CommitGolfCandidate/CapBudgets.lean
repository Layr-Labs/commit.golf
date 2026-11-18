import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.CapOpenProgramRun
import CommitGolfCandidate.CapCheckOracleResources
import CommitGolfCandidate.Budgets

/-! Honest query budgets for the actual cap scheme. Commitment retains the
original paid run, opening is query-free, and the checker has a universal
26-per-record bound (17 lower-record calls: two leaf, one group and fourteen
path calls; at most 8 cap calls), including malformed cap suffixes. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_scheme_commit_same (message : Message) :
    capProgram.scheme.commit message = submission.scheme.commit message := rfl

theorem cap_program_honest_budgets : capProgram.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,commitCalls⟩,committed,rest⟩ := reached
  rw [cap_scheme_commit_same] at committed
  have commitment := scheme_commit_calls oracle message ((root,trapdoor),commitCalls) committed
  by_cases empty : positions.card = 0
  · rw [cap_open_empty_scheme_bytes trapdoor positions empty,oracle_run_pure] at rest
    simp only [support_pure,Set.mem_singleton_iff] at rest
    obtain ⟨opened,rfl,rfl⟩ := rest
    have checker := cap_check_scheme_budget oracle
      ⟨root,positions,message.restrict positions,[]⟩
    dsimp only at commitment checker
    refine ⟨?_,Nat.zero_le _,?_⟩
    · change commitCalls ≤ COMMIT_BUDGET
      rw [commitment]
      decide
    · exact checker.trans (by unfold CHECK_BUDGET; omega)
  · have positive := Nat.pos_of_ne_zero empty
    rw [cap_open_nonempty_scheme_bytes trapdoor positions positive,oracle_run_pure] at rest
    simp only [support_pure,Set.mem_singleton_iff] at rest
    obtain ⟨opened,rfl,rfl⟩ := rest
    have checker := cap_check_scheme_budget oracle
      ⟨root,positions,message.restrict positions,capOpenLoadedBytes trapdoor positions⟩
    dsimp only at commitment checker
    refine ⟨?_,Nat.zero_le _,?_⟩
    · change commitCalls ≤ COMMIT_BUDGET
      rw [commitment]
      decide
    · exact checker.trans (by unfold CHECK_BUDGET; omega)

end CommitGolfCandidate
