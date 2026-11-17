import CommitGolfCandidate.CapMarkInvariant

namespace CommitGolfCandidate
open CommitGolf

def capTreeMarks (leaves : Nat → Bool) (node : Nat) : Bool :=
  if zero : node = 0 then false
  else if internal : node < 256 then
    capTreeMarks leaves (2*node) || capTreeMarks leaves (2*node+1)
  else leaves node
termination_by 256-node
decreasing_by all_goals omega

theorem cap_tree_marks_leaf (leaves : Nat → Bool) (node : Nat)
    (lower : 256 ≤ node) : capTreeMarks leaves node = leaves node := by
  rw [capTreeMarks, dif_neg (by omega : node ≠ 0), dif_neg (Nat.not_lt.mpr lower)]

theorem cap_tree_marks_parent (leaves : Nat → Bool) (node : Nat)
    (positive : 0 < node) (internal : node < 256) :
    capTreeMarks leaves node =
      (capTreeMarks leaves (2*node) || capTreeMarks leaves (2*node+1)) := by
  rw [capTreeMarks, dif_neg (ne_of_gt positive), dif_pos internal]

end CommitGolfCandidate
