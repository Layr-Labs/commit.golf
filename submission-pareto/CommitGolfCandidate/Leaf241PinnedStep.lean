import CommitGolfCandidate.JointOracle241State
import CommitGolfCandidate.PinCallNatCounts

/-! One-step pinned-table answer fibers at width 241, separating forward pair
events from inverse pair and unary events. -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation Finset
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable

private abbrev H := s3PinCallW 241

private theorem fibers :
    (∀ x old, ∃ F : Finset S3State, F.card ≤ 2^1360 ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F) ∧
    (∀ x y, ¬ H.badSpec.single ⟨.fwd,x,y⟩) ∧
    (∀ y old, ∃ F : Finset S3State, F.card ≤ 2^1360 ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F) ∧
    (∀ y, ∃ F : Finset S3State, F.card ≤ 2^896 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F) :=
  PinCall.answer_fibers H (2^1359) (2^896) (2^1344) (2^896) (2^1360)
  (by intro d; simpa only [Nat.reduceSub] using s3_trunc_width_fiber 241 (by decide) d)
  s3_chop_fiber s3_pin_fiber (by norm_num) (by norm_num) (by norm_num)

theorem pinned241_forward_fibers (x : S3State) (old : Permutation.Entry S3State) :
    ∃ F : Finset S3State, F.card ≤ 2^1360 ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F := fibers.1 x old

theorem pinned241_forward_unary (x y : S3State) :
    ¬ H.badSpec.single ⟨.fwd,x,y⟩ := fibers.2.1 x y

theorem pinned241_inverse_fibers (y : S3State) (old : Permutation.Entry S3State) :
    ∃ F : Finset S3State, F.card ≤ 2^1360 ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F := fibers.2.2.1 y old

theorem pinned241_unary_fibers (y : S3State) :
    ∃ F : Finset S3State, F.card ≤ 2^896 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F := fibers.2.2.2 y

theorem pinned241_forward_count (t : Trace S3State) (good : H.badSpec.Good t)
    (x : S3State) (A : Finset S3State) :
    ∑ y ∈ A, ind (¬ H.badSpec.Good (t.stepF x y)) ≤ ((t.length*2^1360 : Nat) : ℝ) := by
  classical
  by_cases cached : x ∈ t.usedIn
  · simp only [Trace.stepF,cached,ite_true,ind_neg (not_not_intro good)]
    simp only [Finset.sum_const_zero]
    positivity
  · simp only [Trace.stepF,cached,ite_false]
    simpa only [Nat.add_zero] using sum_ind_bad_le H.badSpec (2^1360) 0
      (fun y => ⟨.fwd,x,y⟩) (pinned241_forward_fibers x)
      ⟨∅, by simp, fun y h => absurd h.1 (by simp)⟩ t good A

theorem pinned241_inverse_count (t : Trace S3State) (good : H.badSpec.Good t)
    (y : S3State) (A : Finset S3State) :
    ∑ x ∈ A, ind (¬ H.badSpec.Good (t.stepI x y)) ≤
      ((t.length*2^1360+2^896 : Nat) : ℝ) := by
  classical
  by_cases cached : y ∈ t.usedOut
  · simp only [Trace.stepI,cached,ite_true,ind_neg (not_not_intro good)]
    simp only [Finset.sum_const_zero]
    positivity
  · simp only [Trace.stepI,cached,ite_false]
    exact sum_ind_bad_le H.badSpec (2^1360) (2^896) (fun x => ⟨.inv,x,y⟩)
      (pinned241_inverse_fibers y) (pinned241_unary_fibers y) t good A

theorem pinned241_forward_card (t : Trace S3State) (good : H.badSpec.Good t)
    (x : S3State) (A : Finset S3State) :
    (A.filter fun y => ¬ H.badSpec.Good (t.stepF x y)).card ≤ t.length*2^1360 :=
  forward_bad_card H.badSpec (2^1360) pinned241_forward_fibers pinned241_forward_unary t good x A

theorem pinned241_inverse_card (t : Trace S3State) (good : H.badSpec.Good t)
    (y : S3State) (A : Finset S3State) :
    (A.filter fun x => ¬ H.badSpec.Good (t.stepI x y)).card ≤ t.length*2^1360+2^896 :=
  inverse_bad_card H.badSpec (2^1360) (2^896) pinned241_inverse_fibers pinned241_unary_fibers t good y A

end TwoPermutationPrototype.Sampling
