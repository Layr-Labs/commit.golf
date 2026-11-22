import CommitGolf.Artifact
import CommitGolfCandidate.Layout2Closing

namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

private theorem k1_manifest : submission = K1Artifact.submission := rfl

theorem certificate : Certificate submission 72160 504585244 69329 := by
  rw [k1_manifest]
  exact TwoPermutationPrototype.GroupedOpening.Layout2V2.layout2_certificate

end CommitGolf.Challenge
