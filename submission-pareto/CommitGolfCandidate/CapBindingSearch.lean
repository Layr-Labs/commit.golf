import CommitGolfCandidate.CapCheckClaimCollision

/-! The parsed batches of a claim against the actual cap scheme fit the
budgeted searches of `S3CapBinding`: each opening has at most `LENGTH` loaded
records, so the paid pair probe fits the replay ceiling, the leaf replay fits
`s3LeafExtra` and the group replay fits `s6GroupReplay` and `s6GroupExtra`. No
hidden table is used by any of the collision predicates. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
set_option autoImplicit false

theorem cap_claim_left_records_bound (claim : Scheme.Claim) :
    (capCheckLoadedRecords (claimLeft claim)).length ≤ LENGTH := by
  rw [cap_check_loaded_records_length]
  simpa [claimLeft,Index] using Finset.card_le_univ claim.positions₀

theorem cap_claim_right_records_bound (claim : Scheme.Claim) :
    (capCheckLoadedRecords (claimRight claim)).length ≤ LENGTH := by
  rw [cap_check_loaded_records_length]
  simpa [claimRight,Index] using Finset.card_le_univ claim.positions₁

end CommitGolfCandidate
