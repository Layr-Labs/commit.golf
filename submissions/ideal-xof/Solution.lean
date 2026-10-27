import CommitGolf
import CommitGolfCandidate.Xof.XofProof.Certificate

/-! Example submission for the ideal XOF track: a Merkle tree with 256-bit digests. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Scheme := CommitGolf.XofBaseline.merkle

theorem certificate : CommitGolf.TrackCertificate .idealXof submission 76800 2400 :=
  { toCertificate := CommitGolf.XofBaseline.merkle_certificate, inTrack := rfl }

/-- info: 'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end CommitGolf.Challenge
