import CommitGolfCandidate.ReconstructedCommitTrace
import CommitGolfCandidate.Machine
import CommitGolfCandidate.CountingCoins

namespace CommitGolfCandidate.Reconstruction.CommitTrace
open CommitGolf Riscv OracleComp

attribute [local irreducible] ArtifactEncoding.decode execute

private theorem run_commit (s : Submission) (m : Message) : s.run .commit m =
    execute (s.image .commit) (s.steps .commit) (s.initialState .commit m) true := rfl

/-- The trusted game runner records the same public calls as the real interpreter. -/
theorem counted (π : Oracle) (m : Message) (r : Execution × Nat)
    (hr : r ∈ support (π.run (Artifact.submission.run .commit m))) :
    r.1.cycles ≤ 720507500 ∧ r.2 ≤ 56030463 ∧ r.1.exit ≠ .unfinished := by
  obtain ⟨c,q,e⟩ := bounded m r.1 (writer_support (π.world.withAddCost Oracle.callCost) _ r hr)
  rw [run_commit] at hr
  have equal := execute_counted_with_coins π _ _ _ true r hr
  exact ⟨c,equal ▸ q,e⟩

theorem termination_commit (π : Oracle) (m : Message) :
    Pr{let r ← π.run (Artifact.submission.run .commit m)}[r.1.exit ≠ Exit.unfinished] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr
  exact (counted π m r hr).2.2

theorem honest_commit_cycles (π : Oracle) (m : Message) (ps : Positions) :
    Pr{let r ← π.run (Artifact.submission.honestMachine m ps)}[r.1.commitCycles ≤ 720507500] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r hr
  have possible := writer_support (π.world.withAddCost Oracle.callCost) _ r hr
  simp only [Submission.honestMachine,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at possible
  obtain ⟨committed,hc,opened,_,e⟩ := possible
  rw [e]
  exact (bounded m committed hc).1

end CommitGolfCandidate.Reconstruction.CommitTrace
