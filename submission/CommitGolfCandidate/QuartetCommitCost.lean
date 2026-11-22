import CommitGolfCandidate.QuartetCommitJoin
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv OracleComp
attribute [local irreducible] commitBody prePrefix QuartetChain.expansion QuartetChain.chainFinish

/-- Every commitment run succeeds with exactly 522,614,991 cycles and 43,468,241 oracle calls
(1,525,202 chain calls plus Quartet's 41,943,039). -/
theorem exact_cost (message : Message) (result : Execution)
    (hit : result ∈ support (Artifact.submission.run .commit message)) :
    result.exit=.success ∧ result.cycles=522614991 ∧ result.oracleCalls=43468241 := by
  rw [artifact_run] at hit
  simp only [commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
  obtain ⟨_,_,_,_,_,_,rfl⟩ := hit
  exact ⟨rfl,rfl,rfl⟩
end TwoPermutationPrototype.QuartetCommit
