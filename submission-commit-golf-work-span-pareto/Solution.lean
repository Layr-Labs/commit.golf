import CommitGolfCandidate.LegacyBaseline
import CommitGolfDepth.Span
import CommitGolf.Artifact

/-! Serial bootstrap: the same certified machine bytes as submission-pareto.
The exact legacy bridge preserves every security requirement. This is a complete
certificate, not a claim that these images exploit the new parallel operations. -/
namespace CommitGolf.Challenge
open CommitGolf OracleComp

def submission : CommitGolfDepth.Span.Submission :=
  CommitGolfDepth.Span.Submission.ofLegacy CommitGolfCandidate.submission

set_option maxRecDepth 100000 in
theorem submission_matches_artifact : submission = CommitGolf.Artifact.depthSubmission := by
  apply CommitGolfDepth.Span.Submission.ext
  · rfl
  · funext program
    cases program <;> rfl

theorem certificate : CommitGolfDepth.Span.Certificate submission
    102400 3959423012 48670 3959423012 48670 :=
  CommitGolfDepth.Span.Certificate.ofLegacy CommitGolfCandidate.submission
    102400 3959423012 48670 CommitGolfCandidate.LegacyBaseline.certificate

end CommitGolf.Challenge
