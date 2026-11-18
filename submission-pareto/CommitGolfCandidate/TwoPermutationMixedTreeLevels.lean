import CommitGolfCandidate.TwoPermutationMixedTranscript
import CommitGolfCandidate.TwoPermutationOpeningGeometry

/-! Counter-based native lower-path rules agree with node-based mixed projection. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.ShortTree

theorem mixed_lower_parent_full_iff (index : Index) (level : Nat) (inside : level < 16) :
    2 ^ 22 ≤ Opening.lowerNode index level / 2 ↔ level ≤ 1 := by
  have bound : index.val < 16777216 := index.isLt
  interval_cases level <;> norm_num [Opening.lowerNode, LENGTH, LOG_LENGTH] at * <;> omega

theorem mixed_lower_parent_projection (index : Index) (level : Nat) (inside : level < 16)
    (answer : Digest) :
    projectMixed (Opening.lowerNode index level / 2) answer =
      if 15 ≤ 16 - level then answer else padLow answer := by
  by_cases full : level ≤ 1
  · rw [projectMixed_full _ _ ((mixed_lower_parent_full_iff index level inside).mpr full),
      if_pos (by omega)]
  · have short : Opening.lowerNode index level / 2 < 2 ^ 22 :=
      Nat.lt_of_not_ge (fun large => full ((mixed_lower_parent_full_iff index level inside).mp large))
    rw [projectMixed_projected _ _ short, if_neg (by omega)]

theorem mixed_lower_sibling_projected (index : Index) (level : Nat)
    (later : 3 ≤ level) (inside : level < 16) :
    Opening.lowerNode index level ^^^ 1 < 2 ^ 22 := by
  have bound : index.val < 16777216 := index.isLt
  have node : Opening.lowerNode index level < 2 ^ 22 := by
    interval_cases level <;> norm_num [Opening.lowerNode, LENGTH, LOG_LENGTH] at * <;> omega
  exact Nat.xor_lt_two_pow node (show (1 : Nat) < 2 ^ 22 by decide)

end TwoPermutationPrototype.Sampling
