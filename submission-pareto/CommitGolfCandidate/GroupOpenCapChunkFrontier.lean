import CommitGolfCandidate.TwoPermutationTranscript

/-! Frontier of a depth-3 cap subtree (a level-5 node and its 14 descendants) from the byte of its eight leaf
marks. Relative nodes are heap indices 1..15 of the subtree; `chunkNode node r` is the absolute heap index. -/
namespace TwoPermutationPrototype.GroupedOpening
open TwoPermutationPrototype.Sampling

/-- Bit `j` of the leaf mask: leaf `8 node + j` holds a requested group. -/
def leafBit (groups : List Nat) (node j : Nat) : Nat := (capIsMarked groups (8*node+j) 0).toNat

/-- The eight leaf marks of the depth-3 subtree under `node`, as a byte. -/
def leafMask (groups : List Nat) (node : Nat) : Nat :=
  leafBit groups node 0+2*leafBit groups node 1+4*leafBit groups node 2+8*leafBit groups node 3+
    16*leafBit groups node 4+32*leafBit groups node 5+64*leafBit groups node 6+128*leafBit groups node 7

/-- Relative node `r` at height `h` covers a marked leaf of `mask`. -/
def maskMarked (mask r : Nat) : Nat → Bool
  | 0 => mask/2^(r-8)%2==1
  | h+1 => maskMarked mask (2*r) h || maskMarked mask (2*r+1) h

/-- Relative frontier (heap indices, DFS order) of the subtree for leaf mask `mask`. -/
def maskFrontier (mask r : Nat) : Nat → List Nat
  | 0 => if maskMarked mask r 0 then [] else [r]
  | h+1 => if maskMarked mask r (h+1) then maskFrontier mask (2*r) h++maskFrontier mask (2*r+1) h else [r]

/-- Depth of relative node `r` (1..15) below the subtree root. -/
def depthOf (r : Nat) : Nat := if r<2 then 0 else if r<4 then 1 else if r<8 then 2 else 3

/-- Absolute heap index of relative node `r` under `node`. -/
def chunkNode (node r : Nat) : Nat := node*2^(depthOf r)+(r-2^(depthOf r))

/-- The frontier emitted by the block of a marked subtree with leaf mask `mask`. -/
def chunkEntries (mask : Nat) : List Nat := maskFrontier mask 1 3

theorem leaf_bit_le (groups : List Nat) (node j : Nat) : leafBit groups node j ≤ 1 := by
  unfold leafBit; cases capIsMarked groups (8*node+j) 0 <;> decide

theorem leaf_mask_lt (groups : List Nat) (node : Nat) : leafMask groups node<256 := by
  have := leaf_bit_le groups node 0; have := leaf_bit_le groups node 1; have := leaf_bit_le groups node 2
  have := leaf_bit_le groups node 3; have := leaf_bit_le groups node 4; have := leaf_bit_le groups node 5
  have := leaf_bit_le groups node 6; have := leaf_bit_le groups node 7
  unfold leafMask; omega

private theorem mask_bit (groups : List Nat) (node j : Nat) (hj : j<8) :
    leafMask groups node/2^j%2=leafBit groups node j := by
  have := leaf_bit_le groups node 0; have := leaf_bit_le groups node 1; have := leaf_bit_le groups node 2
  have := leaf_bit_le groups node 3; have := leaf_bit_le groups node 4; have := leaf_bit_le groups node 5
  have := leaf_bit_le groups node 6; have := leaf_bit_le groups node 7
  unfold leafMask
  interval_cases j <;> simp only [pow_zero, pow_one, Nat.reducePow] <;> omega

theorem marks_leaf (groups : List Nat) (node r : Nat) (lo : 8 ≤ r) (hi : r<16) :
    capIsMarked groups (chunkNode node r) 0=maskMarked (leafMask groups node) r 0 := by
  have bit := mask_bit groups node (r-8) (by omega)
  have node8 : chunkNode node r=8*node+(r-8) := by
    unfold chunkNode depthOf; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; norm_num; omega
  rw [node8, maskMarked, bit, leafBit]
  cases capIsMarked groups (8*node+(r-8)) 0 <;> rfl

private theorem chunk_children (node r : Nat) (lo : 1 ≤ r) (hi : r<8) :
    2*chunkNode node r=chunkNode node (2*r) ∧ 2*chunkNode node r+1=chunkNode node (2*r+1) := by
  unfold chunkNode depthOf
  interval_cases r <;> norm_num <;> omega

theorem marks_inner (groups : List Nat) (node r h : Nat) (lo : 2^(3-h) ≤ r) (hi : r<2^(4-h)) (small : h ≤ 3) :
    capIsMarked groups (chunkNode node r) h=maskMarked (leafMask groups node) r h := by
  induction h generalizing r with
  | zero => exact marks_leaf groups node r (by simpa using lo) (by simpa using hi)
  | succ h ih =>
    have lo' : 1 ≤ r := le_trans (Nat.one_le_two_pow) lo
    have hi' : r<8 := by
      have : 2^(4-(h+1)) ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨left, right⟩ := chunk_children node r lo' hi'
    have range : 2^(3-h)=2*2^(3-(h+1)) ∧ 2^(4-h)=2*2^(4-(h+1)) := by
      constructor <;> rw [← Nat.pow_succ'] <;> congr 1 <;> omega
    rw [cap_marked_children, right, left, maskMarked,
      ih (2*r) (by omega) (by omega) (by omega), ih (2*r+1) (by omega) (by omega) (by omega)]

theorem frontier_rel (groups : List Nat) (node r h : Nat) (lo : 2^(3-h) ≤ r) (hi : r<2^(4-h)) (small : h ≤ 3) :
    capFrontierNodes groups (chunkNode node r) h=(maskFrontier (leafMask groups node) r h).map (chunkNode node) := by
  induction h generalizing r with
  | zero =>
    rw [capFrontierNodes, maskFrontier, marks_inner groups node r 0 lo hi small]
    split <;> rfl
  | succ h ih =>
    have lo' : 1 ≤ r := le_trans (Nat.one_le_two_pow) lo
    have hi' : r<8 := by
      have : 2^(4-(h+1)) ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    obtain ⟨left, right⟩ := chunk_children node r lo' hi'
    have range : 2^(3-h)=2*2^(3-(h+1)) ∧ 2^(4-h)=2*2^(4-(h+1)) := by
      constructor <;> rw [← Nat.pow_succ'] <;> congr 1 <;> omega
    rw [capFrontierNodes, maskFrontier, marks_inner groups node r (h+1) lo hi small, right, left,
      ih (2*r) (by omega) (by omega) (by omega), ih (2*r+1) (by omega) (by omega) (by omega)]
    split <;> simp

theorem chunk_node_root (node : Nat) : chunkNode node 1=node := by simp [chunkNode, depthOf]

/-- The cap frontier of a level-5 subtree is the block frontier of its leaf mask. -/
theorem chunk_frontier (groups : List Nat) (node : Nat) :
    capFrontierNodes groups node 3=(chunkEntries (leafMask groups node)).map (chunkNode node) := by
  have h := frontier_rel groups node 1 3 (by decide) (by decide) (by decide)
  rwa [chunk_node_root] at h

theorem chunk_marked (groups : List Nat) (node : Nat) :
    capIsMarked groups node 3=maskMarked (leafMask groups node) 1 3 := by
  have h := marks_inner groups node 1 3 (by decide) (by decide) (by decide)
  rwa [chunk_node_root] at h

/-- A marked subtree has a nonzero leaf mask. -/
theorem mask_marked_iff (mask : Nat) (small : mask<256) : maskMarked mask 1 3=true ↔ mask ≠ 0 := by
  revert mask; decide +kernel

end TwoPermutationPrototype.GroupedOpening
