import CommitGolfCandidate.RungACompact
import CommitGolfCandidate.RungAAssembly
import CommitGolfCandidate.RungAOpeningProof
namespace CommitGolf.Challenge
open CommitGolfCandidate.RungA
def submission : CommitGolf.Submission := Artifact.submission
theorem submission_matches_artifact : submission=Artifact.submission := rfl
theorem certificate : Certificate submission 70080 841142282 136043 :=
  Assembly.certified rungAOpening compactCommitLaw
end CommitGolf.Challenge
