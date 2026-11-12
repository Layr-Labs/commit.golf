import CommitGolfCandidate.CapDfsSerialization

/-! Construct the cap tree/view directly from the existing heap and finalized
mark equations. Every internal node uses the same compression function. This
discharges the structural consistency premises of canonical serialization;
actual machine memory still has to be identified with this supplied heap. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capHeapTree (roots : Nat → Digest) : (height node : Nat) → Tree height
  | 0, node => .leaf (roots node)
  | height+1, node =>
      .node (capHeapTree roots height (2*node)) (capHeapTree roots height (2*node+1))

def capHeapView (roots : Nat → Digest) (marked : Nat → Bool) :
    (height node : Nat) → CapView height
  | 0, node => .leaf (if marked node then some (roots node) else none)
  | height+1, node =>
      .node (capHeapView roots marked height (2*node))
        (capHeapView roots marked height (2*node+1))

private theorem child_bounds (height node : Nat)
    (lower : 256 ≤ node * 2^(height+1))
    (upper : (node+1) * 2^(height+1) ≤ 512) :
    0 < node ∧ node < 256 ∧
      256 ≤ 2*node*2^height ∧ (2*node+1)*2^height ≤ 512 ∧
      256 ≤ (2*node+1)*2^height ∧ (2*node+1+1)*2^height ≤ 512 := by
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

theorem cap_heap_tree_root (compress : Compression) (roots : Nat → Digest)
    (parents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (height node : Nat)
    (lower : 256 ≤ node * 2^height) (upper : (node+1) * 2^height ≤ 512) :
    (capHeapTree roots height node).root compress = roots node := by
  induction height generalizing node with
  | zero => rfl
  | succ height ih =>
      obtain ⟨positive, internal, ll, lu, rl, ru⟩ := child_bounds height node lower upper
      simp only [capHeapTree, Tree.root, ih (2*node) ll lu, ih (2*node+1) rl ru]
      exact (parents node positive internal).symm

theorem cap_heap_tree_consistent (compress : Compression) (roots : Nat → Digest)
    (parents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (height node : Nat)
    (lower : 256 ≤ node * 2^height) (upper : (node+1) * 2^height ≤ 512) :
    CapHeapRoots compress roots node (capHeapTree roots height node) := by
  induction height generalizing node with
  | zero => rfl
  | succ height ih =>
      obtain ⟨positive, internal, ll, lu, rl, ru⟩ := child_bounds height node lower upper
      exact ⟨(cap_heap_tree_root compress roots parents (height+1) node lower upper).symm,
        ih (2*node) ll lu, ih (2*node+1) rl ru⟩

theorem cap_heap_view_occupied (roots : Nat → Digest) (marked : Nat → Bool)
    (parents : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (height node : Nat)
    (lower : 256 ≤ node * 2^height) (upper : (node+1) * 2^height ≤ 512) :
    capOccupied (capHeapView roots marked height node) = marked node := by
  induction height generalizing node with
  | zero => cases value : marked node <;> simp [capHeapView, capOccupied, value]
  | succ height ih =>
      obtain ⟨positive, internal, ll, lu, rl, ru⟩ := child_bounds height node lower upper
      simp only [capHeapView, capOccupied, ih (2*node) ll lu, ih (2*node+1) rl ru]
      exact (parents node positive internal).symm

theorem cap_heap_view_consistent (roots : Nat → Digest) (marked : Nat → Bool)
    (parents : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (height node : Nat)
    (lower : 256 ≤ node * 2^height) (upper : (node+1) * 2^height ≤ 512) :
    CapViewMarks marked node (capHeapView roots marked height node) := by
  induction height generalizing node with
  | zero => cases value : marked node <;> simp [capHeapView, CapViewMarks, value]
  | succ height ih =>
      obtain ⟨positive, internal, ll, lu, rl, ru⟩ := child_bounds height node lower upper
      exact ⟨(cap_heap_view_occupied roots marked parents (height+1) node lower upper).symm,
        ih (2*node) ll lu, ih (2*node+1) rl ru⟩

theorem cap_heap_serialization (compress : Compression) (roots : Nat → Digest)
    (marked : Nat → Bool)
    (hashParents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (markParents : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2*node) || marked (2*node+1))) :
    (capControlBoundaries marked 1022 (.visit 1)).map roots =
      capProof compress (capHeapTree roots 8 1) (capHeapView roots marked 8 1) := by
  exact cap_root_serialization compress marked roots _ _
    (cap_heap_view_consistent roots marked markParents 8 1 (by decide) (by decide))
    (cap_heap_tree_consistent compress roots hashParents 8 1 (by decide) (by decide))

end CommitGolfCandidate
