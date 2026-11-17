import Mathlib
import CommitGolfCandidate.CapRankData

namespace CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

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
  capVisitRanks[node]?.getD 1022

def capAdvanceRank (node : Nat) : Nat :=
  capAdvanceRanks[node]?.getD 1022

theorem cap_control_order_length : (capControlOrder 8 1).length = 1022 := by decide

private theorem cap_rank_table :
    ∀ node : Fin 512, 0 < node.val →
      capVisitRank node.val < capAdvanceRank node.val ∧
      capAdvanceRank node.val < 1022 ∧
      (node.val < 256 → capVisitRank (2 * node.val) = capVisitRank node.val + 1) ∧
      (1 < node.val ∧ node.val % 2 = 0 →
        capVisitRank (node.val + 1) = capAdvanceRank node.val + 1) ∧
      (1 < node.val ∧ node.val % 2 = 1 →
        capAdvanceRank (node.val / 2) = capAdvanceRank node.val + 1) := by decide

theorem cap_visit_terminal_rank (node : Nat) (positive : 0 < node)
    (bounded : node < 512) : capVisitRank node < capAdvanceRank node :=
  (cap_rank_table ⟨node, bounded⟩ positive).1

theorem cap_advance_rank_bounded (node : Nat) (positive : 0 < node)
    (bounded : node < 512) : capAdvanceRank node < 1022 :=
  (cap_rank_table ⟨node, bounded⟩ positive).2.1

theorem cap_descend_rank (node : Nat) (positive : 0 < node)
    (internal : node < 256) : capVisitRank (2 * node) = capVisitRank node + 1 :=
  (cap_rank_table ⟨node, by omega⟩ positive).2.2.1 internal

theorem cap_sibling_rank (node : Nat) (nonroot : 1 < node)
    (bounded : node < 512) (even : node % 2 = 0) :
    capVisitRank (node + 1) = capAdvanceRank node + 1 :=
  (cap_rank_table ⟨node, bounded⟩ (Nat.lt_trans (by decide : 0 < 1) nonroot)).2.2.2.1
    ⟨nonroot, even⟩

theorem cap_ascent_rank (node : Nat) (nonroot : 1 < node)
    (bounded : node < 512) (odd : node % 2 = 1) :
    capAdvanceRank (node / 2) = capAdvanceRank node + 1 :=
  (cap_rank_table ⟨node, bounded⟩ (Nat.lt_trans (by decide : 0 < 1) nonroot)).2.2.2.2
    ⟨nonroot, odd⟩

theorem cap_root_done_rank : capAdvanceRank 1 + 1 = 1022 := by decide

end CommitGolfCandidate
