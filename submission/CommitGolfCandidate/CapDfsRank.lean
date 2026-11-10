import Mathlib

/-! A finite, oracle-independent termination measure for the height-seven cap.
The order includes both visits and returns in the complete binary tree. Pruning
an unknown subtree skips forward in this order; it never adds control steps.
These facts concern control only, not instruction execution or memory safety. -/
namespace CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

inductive CapControlEvent where
  | visit (node : Nat)
  | advance (node : Nat)
  deriving DecidableEq

def capControlOrder : Nat → Nat → List CapControlEvent
  | 0, node => [.visit node, .advance node]
  | height + 1, node =>
      [.visit node] ++ capControlOrder height (2 * node) ++
        capControlOrder height (2 * node + 1) ++ [.advance node]

def capVisitRank (node : Nat) : Nat :=
  (capControlOrder 7 1).idxOf (.visit node)

def capAdvanceRank (node : Nat) : Nat :=
  (capControlOrder 7 1).idxOf (.advance node)

/-- The full tree has 255 nodes and exactly 510 visit/return events. -/
theorem cap_control_order_length : (capControlOrder 7 1).length = 510 := by decide

private theorem cap_rank_table :
    ∀ node : Fin 256, 0 < node.val →
      capVisitRank node.val < capAdvanceRank node.val ∧
      capAdvanceRank node.val < 510 ∧
      (node.val < 128 → capVisitRank (2 * node.val) = capVisitRank node.val + 1) ∧
      (1 < node.val ∧ node.val % 2 = 0 →
        capVisitRank (node.val + 1) = capAdvanceRank node.val + 1) ∧
      (1 < node.val ∧ node.val % 2 = 1 →
        capAdvanceRank (node.val / 2) = capAdvanceRank node.val + 1) := by decide

/-- A terminal visit advances, including an unknown internal subtree. -/
theorem cap_visit_terminal_rank (node : Nat) (positive : 0 < node)
    (bounded : node < 256) : capVisitRank node < capAdvanceRank node :=
  (cap_rank_table ⟨node, bounded⟩ positive).1

theorem cap_advance_rank_bounded (node : Nat) (positive : 0 < node)
    (bounded : node < 256) : capAdvanceRank node < 510 :=
  (cap_rank_table ⟨node, bounded⟩ positive).2.1

/-- A marked internal visit descends to its left child. -/
theorem cap_descend_rank (node : Nat) (positive : 0 < node)
    (internal : node < 128) : capVisitRank (2 * node) = capVisitRank node + 1 :=
  (cap_rank_table ⟨node, by omega⟩ positive).2.2.1 internal

/-- Returning from a left child visits the right sibling. -/
theorem cap_sibling_rank (node : Nat) (nonroot : 1 < node)
    (bounded : node < 256) (even : node % 2 = 0) :
    capVisitRank (node + 1) = capAdvanceRank node + 1 :=
  (cap_rank_table ⟨node, bounded⟩ (Nat.lt_trans (by decide : 0 < 1) nonroot)).2.2.2.1
    ⟨nonroot, even⟩

/-- Returning from a right child advances its parent, after any paid hash. -/
theorem cap_ascent_rank (node : Nat) (nonroot : 1 < node)
    (bounded : node < 256) (odd : node % 2 = 1) :
    capAdvanceRank (node / 2) = capAdvanceRank node + 1 :=
  (cap_rank_table ⟨node, bounded⟩ (Nat.lt_trans (by decide : 0 < 1) nonroot)).2.2.2.2
    ⟨nonroot, odd⟩

theorem cap_root_done_rank : capAdvanceRank 1 + 1 = 510 := by decide

end CommitGolfCandidate
