import CommitGolfCandidate.CapDfsBoundaryOrder
import CommitGolfCandidate.CapMultiproof

/-! Canonical boundary-node order selects exactly the semantic cap proof.
The premises identify the finalized occupancy and the original trapdoor heap
with their tree views. Actual memory/population transport remains explicit;
this theorem makes no unrelated-machine certificate claim. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapViewMarks (marked : Nat → Bool) :
    {height : Nat} → Nat → CapView height → Prop
  | _, node, .leaf known => marked node = known.isSome
  | _, node, .node left right =>
      marked node = capOccupied (.node left right) ∧
        CapViewMarks marked (2*node) left ∧
        CapViewMarks marked (2*node+1) right

def CapHeapRoots (compress : Compression) (roots : Nat → Digest) :
    {height : Nat} → Nat → Tree height → Prop
  | _, node, .leaf value => roots node = value
  | _, node, .node left right =>
      roots node = Tree.root compress (.node left right) ∧
        CapHeapRoots compress roots (2*node) left ∧
        CapHeapRoots compress roots (2*node+1) right

theorem cap_subtree_serialization (compress : Compression) (marked : Nat → Bool)
    (roots : Nat → Digest) {height : Nat} (tree : Tree height)
    (view : CapView height) (node : Nat)
    (marks : CapViewMarks marked node view)
    (heap : CapHeapRoots compress roots node tree) :
    (capSubtreeBoundaries marked height node).map roots = capProof compress tree view := by
  induction tree generalizing node with
  | leaf value =>
      cases view with
      | leaf known =>
          change marked node = known.isSome at marks
          change roots node = value at heap
          cases known <;>
            simp [capSubtreeBoundaries, marks, capProof, capOccupied, Tree.root, heap]
  | node left right ihLeft ihRight =>
      cases view with
      | node lview rview =>
          obtain ⟨atNode, leftMarks, rightMarks⟩ := marks
          obtain ⟨atRoot, leftHeap, rightHeap⟩ := heap
          by_cases occupied : capOccupied (.node lview rview) = true
          · have present : marked node = true := atNode.trans occupied
            simp only [capSubtreeBoundaries, present, ↓reduceIte, List.map_append,
              capProof, occupied]
            rw [ihLeft lview (2*node) leftMarks leftHeap,
              ihRight rview (2*node+1) rightMarks rightHeap]
          · have absent : capOccupied (.node lview rview) = false :=
              Bool.eq_false_iff.mpr occupied
            have unmarked : marked node = false := atNode.trans absent
            simp only [capSubtreeBoundaries, unmarked, Bool.false_eq_true, ↓reduceIte,
              List.map_cons, List.map_nil, capProof, absent]
            rw [atRoot]

theorem cap_root_serialization (compress : Compression) (marked : Nat → Bool)
    (roots : Nat → Digest) (tree : Tree 8) (view : CapView 8)
    (marks : CapViewMarks marked 1 view)
    (heap : CapHeapRoots compress roots 1 tree) :
    (capControlBoundaries marked 1022 (.visit 1)).map roots = capProof compress tree view := by
  rw [cap_root_boundary_order]
  exact cap_subtree_serialization compress marked roots tree view 1 marks heap

end CommitGolfCandidate
