import CommitGolf
import CommitGolfCandidate.Permutation.MerkleProof.Certificate

/-! # Example submission: the Merkle baseline

A submission defines `CommitGolf.Challenge.submission` and proves
`CommitGolf.Challenge.certificate` for the scores in `claim.json`. Supporting modules go in
`CommitGolfCandidate/`. -/

namespace CommitGolf.Challenge

def submission : CommitGolf.Scheme := CommitGolf.Baseline.merkle

theorem certificate : CommitGolf.TrackCertificate .idealPermutation submission 76800 2400 :=
  { toCertificate := CommitGolf.Baseline.merkle_certificate, inTrack := rfl }

/-- info: 'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end CommitGolf.Challenge
