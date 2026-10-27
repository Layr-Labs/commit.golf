import CommitGolfCandidate.Permutation.MerkleProof.Honest
import CommitGolfCandidate.Permutation.MerkleProof.Binding

/-! # The Merkle baseline's certificate

The sanity check of the statements: the textbook Merkle tree satisfies all five, with proofs of
`76800` bytes checked with `2400` permutation calls. -/

namespace CommitGolf.Baseline

theorem merkle_certificate : Certificate merkle 76800 2400 where
  completeness := merkle_completeness
  honestBudgets := merkle_honestBudgets
  proofSize := merkle_proofSize
  verificationCost := merkle_verificationCost
  binding := merkle_binding

end CommitGolf.Baseline
