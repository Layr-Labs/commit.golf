import CommitGolf
import CommitGolfBaseline.CompressionProof.Certificate

/-! Example submission for the ideal-compression track: a 512-to-256-bit Merkle tree. -/
namespace CommitGolf.Challenge

def submission : CommitGolf.Scheme := CommitGolf.CompressionBaseline.merkle

theorem certificate : CommitGolf.TrackCertificate .idealCompression submission 76800 2400 :=
  { toCertificate := CommitGolf.CompressionBaseline.merkle_certificate, inTrack := rfl }

/-- info: 'CommitGolf.Challenge.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end CommitGolf.Challenge
