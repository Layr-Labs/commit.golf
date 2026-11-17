import CommitGolfCandidate.CapDfsControl

/-! Recursive subtree segments of the iterative cap control. A segment ends at
its own return event; its caller then performs the sibling/ascent transition.
Unknown nodes consume one visit and skip the complete subtree. This is a pure
order bridge, not yet the memory/serialized-byte refinement. -/
namespace CommitGolfCandidate
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capSubtreeSteps (marked : Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 1
  | height + 1, node =>
      if marked node then
        1 + capSubtreeSteps marked height (2 * node) + 1 +
          capSubtreeSteps marked height (2 * node + 1) + 1
      else 1

def capSubtreeBoundaries (marked : Nat → Bool) : Nat → Nat → List Nat
  | 0, node => if marked node then [] else [node]
  | height + 1, node =>
      if marked node then
        capSubtreeBoundaries marked height (2 * node) ++
          capSubtreeBoundaries marked height (2 * node + 1)
      else [node]

theorem cap_control_run_add (marked : Nat → Bool) (first second : Nat)
    (control : CapDfsControl) :
    capControlRun marked (first + second) control =
      capControlRun marked second (capControlRun marked first control) := by
  induction first generalizing control with
  | zero => simp only [Nat.zero_add, capControlRun]
  | succ first ih =>
      simpa only [Nat.succ_add, capControlRun] using ih (capControlStep marked control)

private theorem subtree_children (height node : Nat)
    (lower : 256 ≤ node * 2^(height+1))
    (upper : (node + 1) * 2^(height+1) ≤ 512) :
    0 < node ∧ node < 256 ∧
      256 ≤ (2*node) * 2^height ∧ ((2*node)+1) * 2^height ≤ 512 ∧
      256 ≤ (2*node+1) * 2^height ∧ ((2*node+1)+1) * 2^height ≤ 512 := by
  have power : 0 < 2^height := Nat.two_pow_pos height
  rw [pow_succ] at lower upper
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem cap_subtree_run_end (marked : Nat → Bool) (height node : Nat)
    (lower : 256 ≤ node * 2^height)
    (upper : (node + 1) * 2^height ≤ 512) :
    capControlRun marked (capSubtreeSteps marked height node) (.visit node) =
      .advance node := by
  induction height generalizing node with
  | zero =>
      have terminal : ¬ node < 256 := by simpa using (Nat.not_lt.mpr lower)
      simp only [capSubtreeSteps, capControlRun, capControlStep]
      simp [terminal]
  | succ height ih =>
      obtain ⟨positive, internal, leftLower, leftUpper, rightLower, rightUpper⟩ :=
        subtree_children height node lower upper
      by_cases present : marked node = true
      · have left := ih (2*node) leftLower leftUpper
        have right := ih (2*node+1) rightLower rightUpper
        have leftStep : capControlStep marked (.advance (2*node)) =
            .visit (2*node+1) := by
          simp only [capControlStep]
          have notRoot : 2*node ≠ 1 := by omega
          simp [notRoot]
        have rightStep : capControlStep marked (.advance (2*node+1)) =
            .advance node := by
          simp only [capControlStep]
          have notRoot : 2*node+1 ≠ 1 := by omega
          simp [notRoot, Nat.add_div, Nat.mul_div_left, Nat.ne_of_gt positive]
        rw [capSubtreeSteps, if_pos present]
        have splitCount :
            1 + capSubtreeSteps marked height (2*node) + 1 +
              capSubtreeSteps marked height (2*node+1) + 1 =
            1 + (capSubtreeSteps marked height (2*node) +
              (1 + (capSubtreeSteps marked height (2*node+1) + 1))) := by omega
        rw [splitCount, cap_control_run_add]
        have firstStep : capControlRun marked 1 (.visit node) = .visit (2*node) := by
          simp [capControlRun, capControlStep, present, internal]
        rw [firstStep,
          cap_control_run_add marked (capSubtreeSteps marked height (2*node))
            (1 + (capSubtreeSteps marked height (2*node+1) + 1)), left,
          cap_control_run_add marked 1 (capSubtreeSteps marked height (2*node+1) + 1)]
        have oneLeft : capControlRun marked 1 (.advance (2*node)) =
            .visit (2*node+1) := by simp only [capControlRun, leftStep]
        rw [oneLeft, cap_control_run_add marked
          (capSubtreeSteps marked height (2*node+1)) 1, right]
        simp only [capControlRun, rightStep]
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp [capSubtreeSteps, absent, capControlRun, capControlStep]

end CommitGolfCandidate
