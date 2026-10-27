import CommitGolfCandidate.Compression.CompressionProof.Honest
import CommitGolfCandidate.Compression.CompressionProof.Binding

/-! # The Merkle baseline's certificate

The sanity check of the statements: the textbook Merkle tree satisfies all five, with proofs of
`76800` bytes checked with `2400` compression function calls. -/

namespace CommitGolf.CompressionBaseline

theorem merkle_certificate : Certificate merkle 76800 2400 where
  completeness := merkle_completeness
  honestBudgets := merkle_honestBudgets
  proofSize := merkle_proofSize
  verificationCost := merkle_verificationCost
  binding := merkle_binding

end CommitGolf.CompressionBaseline
