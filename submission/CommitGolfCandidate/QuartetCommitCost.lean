import CommitGolfCandidate.QuartetCommitJoin
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv OracleComp
attribute [local irreducible] commitBody prePrefix

theorem exact_cost (message : Message) (result : Execution)
    (hit : result ∈ support (Artifact.submission.run .commit message)) :
    result.exit=.success ∧ result.cycles=541679900 ∧ result.oracleCalls=41943039 := by
  rw [artifact_run] at hit
  simp only [commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨_,_,_,_,rfl⟩ := hit
  exact ⟨rfl,rfl,rfl⟩
end TwoPermutationPrototype.QuartetCommit
