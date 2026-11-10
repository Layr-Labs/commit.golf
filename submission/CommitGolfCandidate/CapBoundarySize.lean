import CommitGolfCandidate.CapOpenProofBudget
import CommitGolfCandidate.CapTreeMarksNonempty

/-! The opening's frontier size depends only on occupancy. Root digests and
hash equations are unnecessary for this counting theorem; honest consistency
is required separately for checker completeness and security. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_subtree_boundary_length (compress : Compression) (marked : Nat → Bool)
    {height : Nat} (tree : Tree height) (view : CapView height) (node : Nat)
    (marks : CapViewMarks marked node view) :
    (capSubtreeBoundaries marked height node).length =
      (capProof compress tree view).length := by
  induction tree generalizing node with
  | leaf value =>
      cases view with
      | leaf known =>
          change marked node = known.isSome at marks
          cases known <;>
            simp [capSubtreeBoundaries, marks, capProof, capOccupied]
  | node left right ihLeft ihRight =>
      cases view with
      | node lview rview =>
          obtain ⟨atNode, leftMarks, rightMarks⟩ := marks
          by_cases present : capOccupied (.node lview rview) = true
          · have selected : marked node = true := atNode.trans present
            simp only [capSubtreeBoundaries, selected, ↓reduceIte, List.length_append,
              capProof, present]
            rw [ihLeft lview (2*node) leftMarks, ihRight rview (2*node+1) rightMarks]
          · have absent : capOccupied (.node lview rview) = false :=
              Bool.eq_false_iff.mpr present
            have unmarked : marked node = false := atNode.trans absent
            simp only [capSubtreeBoundaries, unmarked, Bool.false_eq_true, ↓reduceIte,
              capProof, absent, List.length_singleton]

theorem cap_control_occupied_boundary_bound (marked : Nat → Bool)
    (parents : ∀ node, 0 < node → node < 128 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (nonempty : marked 1 = true) :
    (capControlBoundaries marked 510 (.visit 1)).length ≤ 64 := by
  let roots : Nat → Digest := fun _ => 0
  let tree := capHeapTree roots 7 1
  let view := capHeapView roots marked 7 1
  have marks : CapViewMarks marked 1 view :=
    cap_heap_view_consistent roots marked parents 7 1 (by decide) (by decide)
  have occupied : capOccupied view = true :=
    (cap_heap_view_occupied roots marked parents 7 1 (by decide) (by decide)).trans nonempty
  rw [cap_root_boundary_order, cap_subtree_boundary_length (fun _ => 0) marked tree view 1 marks]
  exact cap_occupied_proof_bound (fun _ => 0) tree view occupied

theorem cap_open_requested_boundary_bound (positions : Positions)
    (positive : 0 < positions.card) :
    (capControlBoundaries (capOpenRequestedMarks positions) 510 (.visit 1)).length ≤ 64 :=
  cap_control_occupied_boundary_bound _ (cap_tree_marks_parent _)
    (cap_open_requested_marks_nonempty positions positive)

end CommitGolfCandidate
