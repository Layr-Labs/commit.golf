import CommitGolfCandidate.CapBindingSearch
import CommitGolfCandidate.S3LeafBinding
import CommitGolfCandidate.S6GroupBinding

/-! Binding for the cap machine scheme. A winning claim is caught by the paid
compression probe of both batch replays (two different inputs whose replies
agree on their low 240 bits), by a collision among the replayed leaves, or by a
collision among the replayed group words; the three budgeted searches are
bounded by the lazy truncated-reply birthday argument, by
`s3_leaf_collision_bound` and by `s6_group_collision_bound`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- The submitted machine scheme meets the complete binding requirement against
all classical adversaries and all positive public-query budgets. -/
theorem cap_program_binding : capProgram.scheme.Binding :=
  s3_cap_pair_binding capProgram.scheme
    (fun claim => capCheckLoadedRecords (claimLeft claim))
    (fun claim => capCheckLoadedRecords (claimRight claim))
    (fun claim => capCheckSuffixWords (claimLeft claim) (576*claim.positions₀.card))
    (fun claim => capCheckSuffixWords (claimRight claim) (576*claim.positions₁.card))
    cap_claim_left_records_bound cap_claim_right_records_bound
    cap_check_claim_probe_collision s3_leaf_collision_bound s6_group_collision_bound

end CommitGolfCandidate
