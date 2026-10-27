import CommitGolfCandidate.RandomOracle.RandomOracleProof.Binding

namespace CommitGolf.RandomOracleBaseline

/-- The 512-bit-input Merkle construction, with 256-bit random-oracle outputs. -/
theorem merkle_certificate : Certificate merkle 76800 2400 where
  completeness := merkle_completeness
  honestBudgets := merkle_honestBudgets
  proofSize := merkle_proofSize
  verificationCost := merkle_verificationCost
  binding := merkle_binding

end CommitGolf.RandomOracleBaseline
