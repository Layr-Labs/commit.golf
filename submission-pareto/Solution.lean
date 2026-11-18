import CommitGolf.Artifact
import CommitGolfCandidate.GroupOpenHeader
import CommitGolfCandidate.GroupOpenClosing

namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

private theorem grouped_manifest : submission = MaterializedArtifact.submission := rfl

theorem certificate : Certificate submission 72192 518591774 78922 := by
  rw [grouped_manifest]
  exact TwoPermutationPrototype.GroupedOpening.grouped_certificate TwoPermutationPrototype.GroupedOpening.certifiedHeader

end CommitGolf.Challenge
