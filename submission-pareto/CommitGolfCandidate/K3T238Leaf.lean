import CommitGolfCandidate.K1HideLeafBinding
import CommitGolfCandidate.K3T238Margin

/-!
# Sharp leaf binding of the K1 leaf (both kinds)

`k1_peer_leaf_layout_sharp : PeerLeafLayoutSharp`: a pinned leaf collision of the K1 leaf has
probability at most `q / 2^129` for every fixed compression, `q / 2^130` per leaf kind.

The kind bounds use the same pinned two-call hashes, fibre counts and second-call input counts as
`fixed_compression_pinned_leaf_bound_sf` (with `k1SaltFirstLayout`) and
`fixed_compression_pinned_leaf_bound_a`; only the final union-bound margin changes:
`replay_margin_130` instead of the `q / 2^124` margin.

* Salt-first leaves: `s3PinCall`, `k = 2^1345 + 2^897`, `v = 2^896`.
* A leaves: `aPinCall`, `k = 2^1346`, `v = 2^1216`.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling Finset
open TwoPermutationPrototype.RV64
set_option maxRecDepth 65536
set_option exponentiation.threshold 2100

/-- A bounded program stays below the permutation size. -/
private theorem k1_calls_fit {q calls : Nat} (small : q ≤ 2^120) (replayed : calls ≤ q+2^31) :
    calls < Fintype.card S3State := by
  have room : q + 2^31 < 2^1600 :=
    lt_of_le_of_lt (Nat.add_le_add_right small _) (by norm_num)
  rw [s3_card_state]
  exact lt_of_le_of_lt replayed room

/-- Salt-first leaves (rank ≠ 0): collisions have probability at most `q / 2^130`. -/
theorem k1_leaf_bound_sf_sharp {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitnessOf false result.2] ≤ (q : ENNReal)/2^130 := by
  refine replayed_event_130 compress program (PinnedLeafWitnessOf false) s3PinCall.badSpec q calls bounded
    (pinned_witness_bad_sf k1SaltFirstLayout) ?_
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have raw : st.prob PState.init (fun _ finish => ¬ s3PinCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) ≤
      unionBound (Fintype.card S3State) (2^1345+2^897) (2^896) calls :=
    s3PinCall.prob_bad_le_inv (2^1344) (2^896) (2^1344) (2^896) (2^1345+2^897)
      calls (k1_calls_fit small replayed) s3_trunc_fiber s3_chop_fiber s3_pin_fiber s3_second_inputs
      (by norm_num) (by norm_num) st calls budget.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  exact replay_margin_130 q calls (2^1345+2^897) (2^896) positive small replayed (by norm_num) (by norm_num)

/-- A leaves (rank 0): collisions have probability at most `q / 2^130`. -/
theorem k1_leaf_bound_a_sharp {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitnessOf true result.2] ≤ (q : ENNReal)/2^130 := by
  refine replayed_event_130 compress program (PinnedLeafWitnessOf true) aPinCall.badSpec q calls bounded
    pinned_witness_bad_a ?_
  let st := toStrat compress (recordRows program)
  have budget : st.QB calls := to_strat_QB compress bounded
  have raw : st.prob PState.init (fun _ finish => ¬ aPinCall.badSpec.Good finish.trace ∧ finish.count ≤ calls) ≤
      unionBound (Fintype.card S3State) (2^1346) (2^1216) calls :=
    aPinCall.prob_bad_le_inv (2^1344) (2^1344) (2^1344) (2^1216) (2^1346)
      calls (k1_calls_fit small replayed) s3_trunc_fiber a_chop_fiber a_pin_fiber a_second_inputs
      (by norm_num) (by norm_num) st calls budget.toIQB
  refine raw.trans ?_
  rw [s3_card_state]
  exact replay_margin_130 q calls (2^1346) (2^1216) positive small replayed le_rfl (by norm_num)

/-- Both kinds: a pinned leaf collision has probability at most `q / 2^129`. -/
theorem k1_pinned_leaf_bound_sharp {α : Type}
    (compress : Compression) (program : OracleComp World α) (q calls : Nat) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      PinnedLeafWitness result.2] ≤ (q : ENNReal)/2^129 := by
  let execution := (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))
  change Pr{let result ← execution}[PinnedLeafWitness result.2] ≤ _
  have split := prEvent_mono execution (fun result => PinnedLeafWitness result.2)
    (fun result => PinnedLeafWitnessOf false result.2 ∨ PinnedLeafWitnessOf true result.2)
    (fun _ hit => pinned_leaf_witness_split hit)
  refine split.trans ((prEvent_or_le execution (fun result => PinnedLeafWitnessOf false result.2)
    (fun result => PinnedLeafWitnessOf true result.2)).trans ?_)
  have sf := k1_leaf_bound_sf_sharp compress program q calls positive small replayed bounded
  have a := k1_leaf_bound_a_sharp compress program q calls positive small replayed bounded
  exact (add_le_add sf a).trans_eq (two_halves_130 q)

/-- Leaf binding of the K1 leaf at `q / 2^129`, both kinds. -/
theorem k1_peer_leaf_layout_sharp : PeerLeafLayoutSharp :=
  ⟨fun compress program q calls positive small replayed bounded =>
    k1_pinned_leaf_bound_sharp compress program q calls positive small replayed bounded⟩

end TwoPermutationPrototype.Sampling
