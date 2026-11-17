import CommitGolfCandidate.CapDfsSubtree

namespace CommitGolfCandidate
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capControlBoundaryHead (marked : Nat → Bool) : CapDfsControl → List Nat
  | .visit node => if marked node then [] else [node]
  | _ => []

def capControlBoundaries (marked : Nat → Bool) : Nat → CapDfsControl → List Nat
  | 0, _ => []
  | fuel + 1, control =>
      capControlBoundaryHead marked control ++
        capControlBoundaries marked fuel (capControlStep marked control)

theorem cap_control_boundaries_add (marked : Nat → Bool) (first second : Nat)
    (control : CapDfsControl) :
    capControlBoundaries marked (first + second) control =
      capControlBoundaries marked first control ++
        capControlBoundaries marked second (capControlRun marked first control) := by
  induction first generalizing control with
  | zero => simp only [Nat.zero_add, capControlBoundaries, capControlRun, List.nil_append]
  | succ first ih =>
      simp only [Nat.succ_add, capControlBoundaries, capControlRun, ih, List.append_assoc]

theorem cap_subtree_boundary_order (marked : Nat → Bool) (height node : Nat)
    (lower : 256 ≤ node * 2^height)
    (upper : (node + 1) * 2^height ≤ 512) :
    capControlBoundaries marked (capSubtreeSteps marked height node) (.visit node) =
      capSubtreeBoundaries marked height node := by
  induction height generalizing node with
  | zero => simp only [capSubtreeSteps, capControlBoundaries, capControlBoundaryHead,
      capSubtreeBoundaries, List.append_nil]
  | succ height ih =>
      have power : 0 < 2^height := Nat.two_pow_pos height
      have lower' := lower
      have upper' := upper
      rw [pow_succ] at lower' upper'
      have positive : 0 < node := by nlinarith
      have internal : node < 256 := by nlinarith
      have leftLower : 256 ≤ (2*node) * 2^height := by nlinarith
      have leftUpper : (2*node+1) * 2^height ≤ 512 := by nlinarith
      have rightLower : 256 ≤ (2*node+1) * 2^height := by nlinarith
      have rightUpper : (2*node+1+1) * 2^height ≤ 512 := by nlinarith
      by_cases present : marked node = true
      · have left := ih (2*node) leftLower leftUpper
        have right := ih (2*node+1) rightLower rightUpper
        have leftEnd := cap_subtree_run_end marked height (2*node) leftLower leftUpper
        have rightEnd := cap_subtree_run_end marked height (2*node+1) rightLower rightUpper
        have firstStep : capControlRun marked 1 (.visit node) = .visit (2*node) := by
          simp [capControlRun, capControlStep, present, internal]
        have oneLeft : capControlRun marked 1 (.advance (2*node)) =
            .visit (2*node+1) := by
          have nonroot : 2*node ≠ 1 := by omega
          simp [capControlRun, capControlStep, nonroot]
        rw [capSubtreeSteps, if_pos present, capSubtreeBoundaries, if_pos present]
        have splitCount :
            1 + capSubtreeSteps marked height (2*node) + 1 +
              capSubtreeSteps marked height (2*node+1) + 1 =
            1 + (capSubtreeSteps marked height (2*node) +
              (1 + (capSubtreeSteps marked height (2*node+1) + 1))) := by omega
        rw [splitCount, cap_control_boundaries_add marked 1, firstStep,
          cap_control_boundaries_add marked (capSubtreeSteps marked height (2*node)),
          left, leftEnd, cap_control_boundaries_add marked 1, oneLeft,
          cap_control_boundaries_add marked (capSubtreeSteps marked height (2*node+1)),
          right, rightEnd]
        simp only [capControlBoundaries, capControlBoundaryHead, present, ↓reduceIte,
          List.append_nil, List.nil_append]
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp [capSubtreeSteps, capSubtreeBoundaries, absent, capControlBoundaries,
          capControlBoundaryHead]

theorem cap_subtree_steps_bound (marked : Nat → Bool) (height node : Nat) :
    capSubtreeSteps marked height node + 3 ≤ 4 * 2^height := by
  induction height generalizing node with
  | zero => simp [capSubtreeSteps]
  | succ height ih =>
      have left := ih (2*node)
      have right := ih (2*node+1)
      simp only [capSubtreeSteps, pow_succ]
      split <;> nlinarith [Nat.two_pow_pos height]

theorem cap_control_done_boundaries (marked : Nat → Bool) (fuel : Nat) :
    capControlBoundaries marked fuel .done = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [capControlBoundaries, capControlBoundaryHead, capControlStep,
        List.nil_append, ih]

theorem cap_root_boundary_order (marked : Nat → Bool) :
    capControlBoundaries marked 1022 (.visit 1) = capSubtreeBoundaries marked 8 1 := by
  have ended := cap_subtree_run_end marked 8 1 (by decide) (by decide)
  have ordered := cap_subtree_boundary_order marked 8 1 (by decide) (by decide)
  have bounded := cap_subtree_steps_bound marked 8 1
  have count : capSubtreeSteps marked 8 1 + 1 ≤ 1022 := by
    norm_num at bounded
    omega
  have splitCount : 1022 = (capSubtreeSteps marked 8 1 + 1) +
      (1022 - (capSubtreeSteps marked 8 1 + 1)) := by omega
  rw [splitCount, cap_control_boundaries_add,
    cap_control_boundaries_add marked (capSubtreeSteps marked 8 1), ended, ordered]
  have oneDone : capControlRun marked 1 (.advance 1) = .done := by
    simp [capControlRun, capControlStep]
  rw [cap_control_run_add, ended, oneDone, cap_control_done_boundaries]
  simp only [capControlBoundaries, capControlBoundaryHead, List.append_nil]

end CommitGolfCandidate
