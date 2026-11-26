import CommitGolfCandidate.LegacyBaseline
import CommitGolfDepth.Rounds
import CommitGolf.Artifact

/-! Serial bootstrap: the same certified machine bytes as submission-pareto.
The exact legacy bridge preserves every security requirement. This is a complete
certificate, not a claim that these images exploit the new parallel operations. -/
namespace CommitGolf.Challenge
open CommitGolf OracleComp

def submission : CommitGolfDepth.Rounds.Submission :=
  CommitGolfDepth.Rounds.Submission.ofLegacy CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.depthSubmission := by
  apply CommitGolfDepth.Rounds.Submission.ext
  · rfl
  · funext program
    cases program <;> rfl

private theorem rounds : submission.RoundBounds 150994943 0 := by
  apply CommitGolfDepth.Rounds.legacyRoundBounds_of_support
  · intro message result reached
    exact Nat.le_of_eq (CommitGolfCandidate.commit_input_resources message result reached).2.2
  · intro trapdoor positions _ result reached
    rw [CommitGolfCandidate.opening_execution] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact Nat.le_refl 0

theorem certificate : CommitGolfDepth.Rounds.Certificate submission
    102400 3959423012 48670 150994943 0 :=
  CommitGolfDepth.Rounds.Certificate.ofLegacy CommitGolfCandidate.submission
    102400 3959423012 48670 150994943 0
    CommitGolfCandidate.LegacyBaseline.certificate rounds

end CommitGolf.Challenge
