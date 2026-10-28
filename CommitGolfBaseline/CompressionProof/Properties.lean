import CommitGolfBaseline.CompressionProof.Honest
import CommitGolfBaseline.CompressionProof.Binding

/-! Historical Merkle properties, retained as reference proofs. These do not prove
hiding or eligibility for the current challenge and are not submission certificates. -/

namespace CommitGolf.CompressionBaseline

theorem merkle_properties :
    merkle.Completeness ∧ merkle.HonestBudgets ∧ merkle.ProofSize 76800 ∧
      merkle.VerificationCost 2400 ∧ merkle.Binding :=
  ⟨merkle_completeness, merkle_honestBudgets, merkle_proofSize,
    merkle_verificationCost, merkle_binding⟩

end CommitGolf.CompressionBaseline
