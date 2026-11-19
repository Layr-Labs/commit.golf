import CommitGolfCandidate.JointOracle238State
import CommitGolfCandidate.PinCallNatCounts

/-! One-step pinned-table answer fibers at width 238, separating forward pair
events from inverse pair and unary events. -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation Finset
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
attribute [local instance] Classical.propDecidable

abbrev pairFiber238 : Nat := 2^1362+2^897

private abbrev H := s3PinCallW 238

private theorem fibers :
    (∀ x old, ∃ F : Finset S3State, F.card ≤ pairFiber238 ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F) ∧
    (∀ x y, ¬ H.badSpec.single ⟨.fwd,x,y⟩) ∧
    (∀ y old, ∃ F : Finset S3State, F.card ≤ pairFiber238 ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F) ∧
    (∀ y, ∃ F : Finset S3State, F.card ≤ 2^896 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F) :=
  PinCall.answer_fibers H (2^1362) (2^896) (2^1344) (2^896) (pairFiber238)
  (by intro d; simpa only [Nat.reduceSub] using s3_trunc_width_fiber 238 (by decide) d)
  s3_chop_fiber s3_pin_fiber (by norm_num [pairFiber238]) (by norm_num [pairFiber238]) (by norm_num [pairFiber238])

theorem pinned238_forward_fibers (x : S3State) (old : Permutation.Entry S3State) :
    ∃ F : Finset S3State, F.card ≤ pairFiber238 ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F := fibers.1 x old

theorem pinned238_forward_unary (x y : S3State) :
    ¬ H.badSpec.single ⟨.fwd,x,y⟩ := fibers.2.1 x y

theorem pinned238_inverse_fibers (y : S3State) (old : Permutation.Entry S3State) :
    ∃ F : Finset S3State, F.card ≤ pairFiber238 ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F := fibers.2.2.1 y old

theorem pinned238_unary_fibers (y : S3State) :
    ∃ F : Finset S3State, F.card ≤ 2^896 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F := fibers.2.2.2 y

theorem pinned238_forward_count (t : Trace S3State) (good : H.badSpec.Good t)
    (x : S3State) (A : Finset S3State) :
    ∑ y ∈ A, ind (¬ H.badSpec.Good (t.stepF x y)) ≤ ((t.length*pairFiber238 : Nat) : ℝ) := by
  classical
  by_cases cached : x ∈ t.usedIn
  · simp only [Trace.stepF,cached,ite_true,ind_neg (not_not_intro good)]
    simp only [Finset.sum_const_zero]
    positivity
  · simp only [Trace.stepF,cached,ite_false]
    simpa only [Nat.add_zero] using sum_ind_bad_le H.badSpec (pairFiber238) 0
      (fun y => ⟨.fwd,x,y⟩) (pinned238_forward_fibers x)
      ⟨∅, by simp, fun y h => absurd h.1 (by simp)⟩ t good A

theorem pinned238_inverse_count (t : Trace S3State) (good : H.badSpec.Good t)
    (y : S3State) (A : Finset S3State) :
    ∑ x ∈ A, ind (¬ H.badSpec.Good (t.stepI x y)) ≤
      ((t.length*pairFiber238+2^896 : Nat) : ℝ) := by
  classical
  by_cases cached : y ∈ t.usedOut
  · simp only [Trace.stepI,cached,ite_true,ind_neg (not_not_intro good)]
    simp only [Finset.sum_const_zero]
    positivity
  · simp only [Trace.stepI,cached,ite_false]
    exact sum_ind_bad_le H.badSpec (pairFiber238) (2^896) (fun x => ⟨.inv,x,y⟩)
      (pinned238_inverse_fibers y) (pinned238_unary_fibers y) t good A

theorem pinned238_forward_card (t : Trace S3State) (good : H.badSpec.Good t)
    (x : S3State) (A : Finset S3State) :
    (A.filter fun y => ¬ H.badSpec.Good (t.stepF x y)).card ≤ t.length*pairFiber238 :=
  forward_bad_card H.badSpec (pairFiber238) pinned238_forward_fibers pinned238_forward_unary t good x A

theorem pinned238_inverse_card (t : Trace S3State) (good : H.badSpec.Good t)
    (y : S3State) (A : Finset S3State) :
    (A.filter fun x => ¬ H.badSpec.Good (t.stepI x y)).card ≤ t.length*pairFiber238+2^896 :=
  inverse_bad_card H.badSpec (pairFiber238) (2^896) pinned238_inverse_fibers pinned238_unary_fibers t good y A

end TwoPermutationPrototype.Sampling
