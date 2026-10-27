import CommitGolf
import CommitGolfCandidate.RandomOracle.RandomOracleProof.Certificate

/-! Example submission for the fixed-output RO track: a Merkle tree with 256-bit digests. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Scheme := CommitGolf.RandomOracleBaseline.merkle

theorem certificate : CommitGolf.TrackCertificate .randomOracleFixedOutput submission 76800 2400 :=
  { toCertificate := CommitGolf.RandomOracleBaseline.merkle_certificate, inTrack := rfl }

/-- info: 'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end CommitGolf.Challenge
