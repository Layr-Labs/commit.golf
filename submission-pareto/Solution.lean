import CommitGolf.Artifact
import CommitGolfCandidate.P4OpenHeader
import CommitGolfCandidate.P4OpenClosing

namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

theorem certificate : Certificate submission 67840 606782591 90263 :=
  TwoPermutationPrototype.GroupedOpening.p4_certificate TwoPermutationPrototype.GroupedOpening.certifiedHeader

end CommitGolf.Challenge
