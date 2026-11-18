import CommitGolfCandidate.TwoPermutationWideLeafMeaning

namespace TwoPermutationPrototype.Overlap
open CommitGolf CommitGolf.Riscv OracleComp
open TwoPermutationPrototype.RV64

/-- Complete executable commitment law: uniform salts, root, all heap nodes and all openings' salts. -/
noncomputable def committed : CommitTranscript program :=
  wideVerifiedTranscript WideLeaves.executableLeaves WideLeaves.executableMeaning

/-- Exact successful execution and public-query count for every input and every allowed reply path. -/
theorem commit_resources (message : Message) (result : Execution)
    (reached : result ∈ support (program.run .commit message)) :
    result.exit = .success ∧ result.cycles = 638059030 ∧ result.oracleCalls = 50331647 := by
  have entry : CommitEntry (program.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩
  erw [submission_wide_commit_run WideLeaves.executableLeaves program rfl
    (by decide) message entry] at reached
  simp only [wideCommitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨salts,_,s,_,rfl⟩ := reached
  exact ⟨rfl,rfl,rfl⟩

end TwoPermutationPrototype.Overlap
