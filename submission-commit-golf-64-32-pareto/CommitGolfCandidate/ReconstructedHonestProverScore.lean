import CommitGolfCandidate.ReconstructedHonestOpeningScore
import CommitGolfCandidate.ReconstructedCommitScored

namespace CommitGolfCandidate.Reconstruction.HonestProverScore
open CommitGolf OracleComp

/-- Both costs are measured in the same official machine game. -/
theorem tight : Artifact.submission.ProverCycles 1489523308 210404 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r run
  exact ⟨(OracleComp.prEvent_eq_one_iff _ _).mp (CommitTrace.honest_commit_cycles oracle message positions) r run,
    (OracleComp.prEvent_eq_one_iff _ _).mp (HonestOpeningScore.scored oracle message positions batch) r run⟩

/-- The 65,544-byte submission's declared resource field: 1,489,523,308 commitment and
210,404 opening cycles at 30-cycle permutations (the `tight` bounds). -/
theorem profile : Artifact.submission.ProverCycles 1489523308 210404 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro r run
  obtain ⟨commit,opening⟩ := (OracleComp.prEvent_eq_one_iff _ _).mp (tight oracle message positions batch) r run
  exact ⟨commit.trans (by decide),opening.trans (by decide)⟩

end CommitGolfCandidate.Reconstruction.HonestProverScore
