import CommitGolfCandidate.ChainedCommitExecution

/-! Whole commitment execution for the exact delivered artifact and its actual entry ABI. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64

theorem artifact_commit_entry (message : Message) :
    CommitEntry (Artifact.submission.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩

theorem artifact_commit_run (message : Message) :
    Artifact.submission.run .commit message =
      chainedCommitTrace (Artifact.submission.initialState .commit message) := by
  apply chained_commit_submission_run Artifact.submission rfl
  · rw [chained_commit_fuel]
    decide
  · exact artifact_commit_entry message

theorem artifact_commit_supported (message : Message) (result : Execution)
    (reached : result ∈ support (Artifact.submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 2425124556 ∧ result.oracleCalls = 102382335 := by
  rw [artifact_commit_run] at reached
  simp only [chainedCommitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨seed,_,last,_,state,_,rfl⟩ := reached
  exact ⟨rfl,rfl,rfl⟩

end CommitGolfCandidate.Chained.Native
