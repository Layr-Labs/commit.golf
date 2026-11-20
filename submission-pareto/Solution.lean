import CommitGolf.Artifact
import CommitGolfCandidate.GroupOpenHeader
import CommitGolfCandidate.GroupOpenClosing

namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

private theorem k1_manifest : submission = K1Artifact.submission := rfl

theorem certificate : Certificate submission 72160 504585244 122262 := by
  rw [k1_manifest]
  exact TwoPermutationPrototype.GroupedOpening.grouped_certificate TwoPermutationPrototype.GroupedOpening.certifiedHeader

end CommitGolf.Challenge
