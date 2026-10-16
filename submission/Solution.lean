import CommitGolf
import CommitGolfBaseline

/-! # Example submission: the Merkle baseline

A submission defines `CommitGolf.Challenge.submission` and proves
`CommitGolf.Challenge.certificate` for the scores in `claim.json`. Supporting modules go in
`CommitGolfCandidate/`. -/

namespace CommitGolf.Challenge

def submission : CommitGolf.Scheme := CommitGolf.Baseline.merkle

theorem certificate : CommitGolf.Certificate submission 76800 2400 :=
  CommitGolf.Baseline.merkle_certificate

end CommitGolf.Challenge
