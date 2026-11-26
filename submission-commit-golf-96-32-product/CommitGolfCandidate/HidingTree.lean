import CommitGolfCandidate.HeapModel

/-! A memory-independent description of the honest Merkle tree. The hiding proof
can reason about salted leaves and their ancestors; machine refinement must still
identify the emitted root and proof with this tree. -/
namespace CommitGolfCandidate
open CommitGolf

/-- The complete binary heap, with leaves at slots `leafCount` through
`2*leafCount-1`. Slot zero and out-of-range slots are unused. -/
def referenceHeap (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (node : Nat) : Digest :=
  if branch : 0 < node ∧ node < leafCount then
    combine compress (referenceHeap compress leafCount leaf (2*node))
      (referenceHeap compress leafCount leaf (2*node+1))
  else if leafCount ≤ node ∧ node < 2*leafCount then leaf (node-leafCount)
  else 0
termination_by 2*leafCount-node
decreasing_by all_goals omega

theorem reference_heap_parent (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (node : Nat) (positive : 0 < node) (below : node < leafCount) :
    referenceHeap compress leafCount leaf node =
      combine compress (referenceHeap compress leafCount leaf (2*node))
        (referenceHeap compress leafCount leaf (2*node+1)) := by
  rw [referenceHeap, dif_pos ⟨positive, below⟩]

theorem reference_heap_leaf (compress : Compression) (leafCount : Nat)
    (leaf : Nat → Digest) (index : Nat) (inside : index < leafCount) :
    referenceHeap compress leafCount leaf (leafCount+index) = leaf index := by
  rw [referenceHeap, dif_neg (by omega), if_pos (by omega)]
  congr 1
  omega

/-- Parent consistency and leaf contents uniquely determine every used heap slot.
No injectivity or random-oracle property of compression is required. -/
theorem heap_eq_reference (compress : Compression) (leafCount : Nat)
    (leaf heap : Nat → Digest)
    (parents : ∀ node, 0 < node → node < leafCount →
      heap node = combine compress (heap (2*node)) (heap (2*node+1)))
    (leaves : ∀ index, index < leafCount → heap (leafCount+index) = leaf index)
    (node : Nat) (positive : 0 < node) (inside : node < 2*leafCount) :
    heap node = referenceHeap compress leafCount leaf node := by
  by_cases branch : node < leafCount
  · rw [parents node positive branch, reference_heap_parent _ _ _ _ positive branch]
    congr 1
    · exact heap_eq_reference compress leafCount leaf heap parents leaves (2*node)
        (by omega) (by omega)
    · exact heap_eq_reference compress leafCount leaf heap parents leaves (2*node+1)
        (by omega) (by omega)
  · have index : node-leafCount < leafCount := by omega
    have address : leafCount+(node-leafCount) = node := by omega
    rw [← address, leaves _ index, reference_heap_leaf _ _ _ _ index]
termination_by 2*leafCount-node
decreasing_by all_goals omega

/-- The mathematical heap for this submission, using exactly its four-block
salted leaf hash and the same compression function for all internal nodes. -/
def saltedHeap (compress : Compression) (message : Message) (salt : Index → Digest) :
    Nat → Digest :=
  referenceHeap compress LENGTH fun index =>
    if inside : index < LENGTH then
      leafDigest compress (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
    else 0

theorem salted_heap_leaf (compress : Compression) (message : Message)
    (salt : Index → Digest) (index : Index) :
    saltedHeap compress message salt (LENGTH+index.val) =
      leafDigest compress (salt index) (message index) := by
  rw [saltedHeap, reference_heap_leaf _ _ _ _ index.isLt, dif_pos index.isLt]

/-- Every sibling read by a valid authentication path is a used heap slot. -/
theorem heap_sibling_bounds (leafCount node : Nat) (positive : 2 ≤ node)
    (inside : node < 2*leafCount) : 0 < node ^^^ 1 ∧ node ^^^ 1 < 2*leafCount := by
  by_cases even : node%2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · have odd : node%2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr odd)]
    omega

theorem opening_sibling_bounds (index : Index) (level : Nat) (inside : level < LOG_LENGTH) :
    0 < ((LENGTH+index.val)/2^level) ^^^ 1 ∧
      ((LENGTH+index.val)/2^level) ^^^ 1 < 2*LENGTH := by
  have indexBound := index.isLt
  have powerPositive : 0 < 2^level := by positivity
  have powerBound : 2^(level+1) ≤ LENGTH :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have doubled : 2^(level+1) = 2*2^level := by rw [Nat.pow_succ]; omega
  have lower : 2 ≤ (LENGTH+index.val)/2^level := by
    rw [doubled] at powerBound
    exact (Nat.le_div_iff_mul_le powerPositive).mpr (by omega)
  have upper : (LENGTH+index.val)/2^level < 2*LENGTH :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact heap_sibling_bounds LENGTH _ lower upper

end CommitGolfCandidate
