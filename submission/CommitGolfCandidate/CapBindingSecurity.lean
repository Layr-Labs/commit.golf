import CommitGolfCandidate.CapBindingSearch
import CommitGolfCandidate.S3LeafBinding

/-! Binding for the cap machine scheme with the stage-3 permutation leaf. A
winning claim is caught by the paid compression probe of both batch replays or
by a collision among the replayed leaves; the two budgeted searches are bounded
by the lazy compression birthday argument and by `s3_leaf_collision_bound`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- The submitted machine scheme meets the complete binding requirement against
all classical adversaries and all positive public-query budgets. -/
theorem cap_program_binding : capProgram.scheme.Binding :=
  s3_cap_pair_binding capProgram.scheme
    (fun claim => capCheckLoadedRecords (claimLeft claim))
    (fun claim => capCheckLoadedRecords (claimRight claim))
    (fun claim => capCheckSuffixWords (claimLeft claim) (544*claim.positions₀.card))
    (fun claim => capCheckSuffixWords (claimRight claim) (544*claim.positions₁.card))
    cap_claim_left_records_bound cap_claim_right_records_bound
    cap_check_claim_probe_collision s3_leaf_collision_bound

end CommitGolfCandidate
