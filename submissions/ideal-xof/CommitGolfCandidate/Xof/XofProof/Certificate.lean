import CommitGolfCandidate.Xof.XofProof.Binding

namespace CommitGolf.XofBaseline

/-- The 512-bit-input Merkle construction, requesting 256-bit XOF outputs. -/
theorem merkle_certificate : Certificate merkle 76800 2400 where
  completeness := merkle_completeness
  honestBudgets := merkle_honestBudgets
  proofSize := merkle_proofSize
  verificationCost := merkle_verificationCost
  binding := merkle_binding

end CommitGolf.XofBaseline
