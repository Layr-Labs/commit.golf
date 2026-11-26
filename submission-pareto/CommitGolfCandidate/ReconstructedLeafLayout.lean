import CommitGolfCandidate.TwoPermutationPinnedLeafWidth
import CommitGolfCandidate.TwoPermutationPinnedPeerLayout

namespace CommitGolfCandidate.Reconstruction.LeafLayout
open CommitGolf CommitGolfCandidate OracleComp MeasureTheory
open TwoPermutationPrototype.Sampling

set_option exponentiation.threshold 2100
set_option maxHeartbeats 2000000

/-- The public forward/inverse permutation bound at the actual 240-bit leaf width,
including room for two checker replays of up to 2^31 calls each. -/
theorem leaf_margin (q queries : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (count : queries ≤ q + 2^32) :
    pinnedWidthTerm 240 queries ≤ ((q : ℝ)*(129/256))/2^120 := by
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qUpper : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have nonneg : (0 : ℝ) ≤ queries := by positivity
  have terms : (queries : ℝ) ≤ (q : ℝ) + 2^32 := by exact_mod_cast count
  have queriesUpper : (queries : ℝ) ≤ 2^121 := by
    have threshold : (2 : ℝ)^120 + 2^32 ≤ 2^121 := by norm_num
    linarith
  have denominator : (2 : ℝ)^1600 - 2^121 ≤ 2^1600-(queries : ℝ) := by linarith
  have denominatorPos : (0 : ℝ) < 2^1600-(queries : ℝ) := by
    have : (0 : ℝ) < 2^1600 - 2^121 := by norm_num
    linarith
  have fiber : (2 : ℝ)^(1600-240) ≤ 2^1360 :=
    by norm_num
  have squareBound : (queries : ℝ)^2 ≤ (q : ℝ)*(2^120 + 2^67) := by
    let extra : ℝ := 2^32
    have leSum : (queries : ℝ) ≤ q + extra := terms
    have sq := mul_le_mul leSum leSum nonneg (by positivity)
    have qsq := mul_le_mul_of_nonneg_right qUpper qNonneg
    have esq : 2*extra*q + extra^2 ≤ q*2^67 := by
      have e1 : 2*extra ≤ 2^33 := by norm_num [extra]
      have e2 : extra^2 ≤ 2^64 := by norm_num [extra]
      nlinarith
    nlinarith
  have linearBound : (queries : ℝ) ≤ (q : ℝ)*2^33 := by
    nlinarith
  have kBound : (2 : ℝ)^(1600-240) + 2^1345 + 2^897 ≤ 2^1360 + 2^1345 + 2^897 := by linarith
  have pairs : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-240) + 2^1345 + 2^897) ≤
      (queries : ℝ)^2 / 2 * (2^1360 + 2^1345 + 2^897) := by
    have k0 : (0 : ℝ) ≤ 2^(1600-240) + 2^1345 + 2^897 := by positivity
    have : (queries : ℝ) * ((queries : ℝ) - 1) / 2 ≤ (queries : ℝ)^2 / 2 := by nlinarith
    calc _ ≤ (queries : ℝ)^2 / 2 * (2^(1600-240) + 2^1345 + 2^897) := mul_le_mul_of_nonneg_right this k0
      _ ≤ _ := mul_le_mul_of_nonneg_left kBound (by positivity)
  have total : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-240) + 2^1345 + 2^897) + (queries : ℝ)*2^896 ≤
      (q : ℝ) * ((2^120 + 2^67) * (2^1360 + 2^1345 + 2^897) / 2 + 2^929) := by
    have a := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ (2^1360 + 2^1345 + 2^897)/2)
    have c := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^896)
    nlinarith
  have constant : (2^120 + 2^67 : ℝ) * (2^1360 + 2^1345 + 2^897) / 2 + 2^929 ≤ (129/256) / 2^120 * (2^1600 - 2^121) := by
    norm_num
  unfold pinnedWidthTerm
  rw [div_le_iff₀ denominatorPos]
  have scaled := mul_le_mul_of_nonneg_left constant qNonneg
  have den := mul_le_mul_of_nonneg_left denominator (by positivity : (0 : ℝ) ≤ ((q : ℝ)*(129/256))/2^120)
  have eq : (q : ℝ) * ((129/256) / 2^120 * (2^1600 - 2^121)) = ((q : ℝ)*(129/256))/2^120 * (2^1600 - 2^121) := by ring
  linarith


/-- A conflicting pair in the recorded leaf rows has probability within this budget
for the actual pinned layout, allowing all 128-bit salt words (including 120-bit salts). -/
theorem leaf_replay_bound {α : Type} (compression : Compression) (program : OracleComp World α)
    (q calls : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) (replayed : calls ≤ q + 2^32)
    (bounded : PublicQueryBound (recordRows program) calls) :
    Pr{let result ← (do let p ← $ᵗ Perm; fixedOracleRun ⟨compression,p⟩ (recordRows program))}[
      PinnedLeafWitnessW 240 result.2] ≤ ENNReal.ofReal (((q : ℝ)*(129/256))/2^120) :=
  pinned_leaf_probability_width 240 (by decide) ⟨pinnedPeerSalt,pinned_first_peer,pinned_second_peer⟩
    compression program calls (by omega) _ (leaf_margin q calls positive small replayed) bounded

end CommitGolfCandidate.Reconstruction.LeafLayout
