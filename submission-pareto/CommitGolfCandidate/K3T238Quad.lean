import CommitGolfCandidate.QuadReplay
import CommitGolfCandidate.K3T238Margin

/-!
# Sharp quartet-collision bound

`fixed_compression_quad_bound_at` bounds a quartet collision of one node parity by `q / 2^124`, but
its union bound (`2^1344`-element node fibers and `2^1024` quartet inputs over the full 1600-bit
state) is far smaller. Routing the same trace argument through `replay_margin_130` gives `q / 2^130`
per parity and `q / 2^129` for both.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling Finset
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

/-- A quartet collision under the node truncation of one group costs at most `q / 2^130`. -/
theorem fixed_compression_quad_bound_at_sharp {α : Type} (group : Nat) (compress : Compression)
    (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      QuadWitnessAt group result.2] ≤ (q : ENNReal)/2^130 := by
  refine replayed_event_130 compress program (QuadWitnessAt group) (quadNodeCall group).badSpec
    q calls bounded (fun _ _ => quad_witness_bad) ?_
  have fits : calls < Fintype.card S3State := by rw [s3_card_state]; omega
  refine (quad_bad_trace_bound group (toStrat compress (recordRows program)) calls fits).trans ?_
  rw [s3_card_state]
  exact replay_margin_130 q calls _ _ positive small replayed
    (Nat.pow_le_pow_right (by norm_num) (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-- Both node parities together: a quartet collision costs at most `q / 2^129`. -/
theorem fixed_compression_quad_bound_sharp {α : Type} (compress : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q+2^31)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))}[
      QuadWitness result.2] ≤ (q : ENNReal)/2^129 := by
  let execution := (do let p ← $ᵗ Perm; fixedOracleRun ⟨compress,p⟩ (recordRows program))
  change Pr{let result ← execution}[QuadWitness result.2] ≤ _
  have split := prEvent_mono execution (fun result => QuadWitness result.2)
    (fun result => QuadWitnessAt 0 result.2 ∨ QuadWitnessAt 1 result.2)
    (fun _ hit => quad_witness_split hit)
  refine split.trans ((prEvent_or_le execution (fun result => QuadWitnessAt 0 result.2)
    (fun result => QuadWitnessAt 1 result.2)).trans ?_)
  have even := fixed_compression_quad_bound_at_sharp 0 compress program q calls positive small replayed bounded
  have odd := fixed_compression_quad_bound_at_sharp 1 compress program q calls positive small replayed bounded
  exact (add_le_add even odd).trans_eq (two_halves_130 q)

end TwoPermutationPrototype.Sampling
