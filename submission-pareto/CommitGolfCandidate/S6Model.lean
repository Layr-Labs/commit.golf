import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.S6Tree

/-! The committed tree as pure functions. Leaf digests (`s3LeafDigest` of the salted leaf), one group digest per
four consecutive leaves, and the binary heap of depth 22 above the 2^22 group digests, whose internal nodes keep
240 bits (`s6Compress`). An opening record authenticates one leaf by its salt, the three other leaf digests of its
group and the 14 siblings of the group node; its root is the cap-level node `256 + index / 2^16`. -/
namespace CommitGolfCandidate
open CommitGolf

def s6LeafValues (permutation : Perm) (message : Message) (salt : Index → Digest) (index : Nat) : Digest :=
  if inside : index < LENGTH then s3LeafDigest permutation (salt ⟨index, inside⟩) (message ⟨index, inside⟩) else 0
def s6GroupValues (permutation : Perm) (leaf : Nat → Digest) (group : Nat) : Digest :=
  s6GroupDigest permutation (leaf (4*group)) (leaf (4*group+1)) (leaf (4*group+2)) (leaf (4*group+3))
/-- The whole tree as a heap: nodes 1 .. 2^22-1 internal, nodes 2^22 .. 2^23-1 the group digests. -/
def s6Heap (compress : Compression) (permutation : Perm) (message : Message) (salt : Index → Digest) : Nat → Digest :=
  referenceHeap (s6Compress compress) (2^22) (s6GroupValues permutation (s6LeafValues permutation message salt))

theorem s6_leaf_values_index (permutation : Perm) (message : Message) (salt : Index → Digest)
    (index : Index) :
    s6LeafValues permutation message salt index.val = s3LeafDigest permutation (salt index) (message index) := by
  rw [s6LeafValues, dif_pos index.isLt]

theorem s6_heap_parent (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (node : Nat) (positive : 0 < node) (below : node < 2^22) :
    s6Heap compress permutation message salt node =
      combine (s6Compress compress) (s6Heap compress permutation message salt (2*node))
        (s6Heap compress permutation message salt (2*node+1)) :=
  reference_heap_parent _ _ _ _ positive below

theorem s6_heap_group (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (group : Nat) (inside : group < 2^22) :
    s6Heap compress permutation message salt (2^22+group) =
      s6GroupValues permutation (s6LeafValues permutation message salt) group :=
  reference_heap_leaf _ _ _ _ inside

/-- Truncated parent consistency and the group digests determine every heap node. -/
theorem s6_heap_eq (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (heap : Nat → Digest)
    (parents : ∀ node, 0 < node → node < 2^22 →
      heap node = combine (s6Compress compress) (heap (2*node)) (heap (2*node+1)))
    (groups : ∀ group, group < 2^22 →
      heap (2^22+group) = s6GroupValues permutation (s6LeafValues permutation message salt) group)
    (node : Nat) (positive : 0 < node) (inside : node < 2^23) :
    heap node = s6Heap compress permutation message salt node :=
  heap_eq_reference _ _ _ heap parents groups node positive (by omega)

/-- Leaf number of the `k`-th other leaf (`k < 3`) of the group of `index`, in increasing leaf order. -/
def s6OtherLeaf (index k : Nat) : Nat :=
  4*(index/4) + (if k < index%4 then k else k+1)

/-- The window of a record's group call: 72 zero bytes, then the leaf's own digest at place `index % 4` and the
three supplied digests at the other places in increasing order. -/
def s6RecordWindow (own : Digest) (index : Nat) (others : Fin 3 → Digest) : BitVec PERMUTATION_WIDTH :=
  if index%4 = 0 then s6GroupInput own (others 0) (others 1) (others 2)
  else if index%4 = 1 then s6GroupInput (others 0) own (others 1) (others 2)
  else if index%4 = 2 then s6GroupInput (others 0) (others 1) own (others 2)
  else s6GroupInput (others 0) (others 1) (others 2) own

/-- The group digest of a record: low 32 bytes of the permutation on its group window. -/
def s6RecordGroup (permutation : Perm) (salt : Digest) (value : Entry) (index : Nat)
    (others : Fin 3 → Digest) : Digest :=
  BitVec.ofNat 256 (permutation (s6RecordWindow (s3LeafDigest permutation salt value) index others)).toNat

/-- The record's group digest is `s6GroupDigest` of the four digests in place order. -/
theorem s6_record_group_digest (permutation : Perm) (salt : Digest) (value : Entry) (index : Nat)
    (others : Fin 3 → Digest) :
    s6RecordGroup permutation salt value index others =
      if index%4 = 0 then
        s6GroupDigest permutation (s3LeafDigest permutation salt value) (others 0) (others 1) (others 2)
      else if index%4 = 1 then
        s6GroupDigest permutation (others 0) (s3LeafDigest permutation salt value) (others 1) (others 2)
      else if index%4 = 2 then
        s6GroupDigest permutation (others 0) (others 1) (s3LeafDigest permutation salt value) (others 2)
      else
        s6GroupDigest permutation (others 0) (others 1) (others 2) (s3LeafDigest permutation salt value) := by
  unfold s6RecordGroup s6RecordWindow s6GroupDigest
  split_ifs <;> rfl

/-- The path of a record above its group node: 14 levels; the direction at level `j` is bit `j` of `index / 4`. -/
def s6RecordPath (index : Nat) (sibling : Fin 14 → Digest) : List (Bool × Digest) :=
  List.ofFn fun level : Fin 14 => ((index/4).testBit level.val, sibling level)

/-- The cap-level root of a record: its group digest, then 14 steps of the node compression `compress`
(the tree's is `s6Compress oracle.compression`). -/
def s6RecordRoot (compress : Compression) (permutation : Perm) (salt : Digest) (value : Entry)
    (index : Nat) (others : Fin 3 → Digest) (sibling : Fin 14 → Digest) : Digest :=
  climb compress (s6RecordGroup permutation salt value index others) (s6RecordPath index sibling)

/-- Sibling `level` (bottom-up) of the group node of leaf `index` in a heap. -/
def s6Sibling (heap : Nat → Digest) (index : Nat) (level : Fin 14) : Digest :=
  heap (((2^22+index/4)/2^level.val) ^^^ 1)

theorem s6_record_path_length (index : Nat) (sibling : Fin 14 → Digest) :
    (s6RecordPath index sibling).length = 14 := by
  simp [s6RecordPath]

theorem s6_record_path_directions (index : Nat) (sibling : Fin 14 → Digest) :
    (s6RecordPath index sibling).map Prod.fst = (List.range 14).map (index/4).testBit := by
  rw [s6RecordPath, List.map_ofFn, List.ofFn_eq_map]
  change (List.finRange 14).map ((index/4).testBit ∘ Fin.val) = _
  rw [← List.map_map, List.map_coe_finRange_eq_range]

private theorem other_leaf_values (index : Nat) :
    (index%4 = 0 → s6OtherLeaf index 0 = 4*(index/4)+1 ∧ s6OtherLeaf index 1 = 4*(index/4)+2 ∧
      s6OtherLeaf index 2 = 4*(index/4)+3) ∧
    (index%4 = 1 → s6OtherLeaf index 0 = 4*(index/4) ∧ s6OtherLeaf index 1 = 4*(index/4)+2 ∧
      s6OtherLeaf index 2 = 4*(index/4)+3) ∧
    (index%4 = 2 → s6OtherLeaf index 0 = 4*(index/4) ∧ s6OtherLeaf index 1 = 4*(index/4)+1 ∧
      s6OtherLeaf index 2 = 4*(index/4)+3) ∧
    (index%4 = 3 → s6OtherLeaf index 0 = 4*(index/4) ∧ s6OtherLeaf index 1 = 4*(index/4)+1 ∧
      s6OtherLeaf index 2 = 4*(index/4)+2) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp only [s6OtherLeaf, h] <;> norm_num

/-- With the honest other digests, the record's group digest is the group digest of the tree. -/
theorem s6_record_group_honest (permutation : Perm) (leaf : Nat → Digest) (salt : Digest)
    (value : Entry) (index : Nat) (own : leaf index = s3LeafDigest permutation salt value) :
    s6RecordGroup permutation salt value index (fun k => leaf (s6OtherLeaf index k.val)) =
      s6GroupValues permutation leaf (index/4) := by
  obtain ⟨h0, h1, h2, h3⟩ := other_leaf_values index
  have split : index = 4*(index/4)+index%4 := (Nat.div_add_mod index 4).symm
  rw [s6_record_group_digest, s6GroupValues, ← own]
  by_cases r0 : index%4 = 0
  · obtain ⟨a, b, c⟩ := h0 r0
    rw [if_pos r0]
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, a, b, c]
    rw [show 4*(index/4) = index by omega]
  · rw [if_neg r0]
    by_cases r1 : index%4 = 1
    · obtain ⟨a, b, c⟩ := h1 r1
      rw [if_pos r1]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, a, b, c]
      rw [show 4*(index/4)+1 = index by omega]
    · rw [if_neg r1]
      by_cases r2 : index%4 = 2
      · obtain ⟨a, b, c⟩ := h2 r2
        rw [if_pos r2]
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, a, b, c]
        rw [show 4*(index/4)+2 = index by omega]
      · have r3 : index%4 = 3 := by omega
        obtain ⟨a, b, c⟩ := h3 r3
        rw [if_neg r2]
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, a, b, c]
        rw [show 4*(index/4)+3 = index by omega]

theorem s6_record_path_heap (heap : Nat → Digest) (index : Nat) (inside : index < 2^24) :
    s6RecordPath index (s6Sibling heap index) = heapPath heap (2^22+index/4) 14 := by
  apply List.ext_getElem
  · rw [s6_record_path_length, heap_path_length]
  · intro level leftBound rightBound
    have below : level < 14 := by simpa only [s6_record_path_length] using leftBound
    rw [heap_path_get _ _ _ _ below]
    simp only [s6RecordPath, List.getElem_ofFn, s6Sibling]
    apply Prod.ext
    · exact (heap_leaf_direction 22 (index/4) level (by omega) (by omega)).symm
    · rfl

/-- The record of `index` with the heap's siblings and the tree's other leaf digests climbs to the cap-level
node `256 + index / 2^16` of any heap whose internal nodes are the `compress`-parents of their children and
whose group node is the group digest of `leaf`. -/
theorem s6_record_root_heap (compress : Compression) (permutation : Perm) (heap leaf : Nat → Digest)
    (parents : ∀ node, 0 < node → node < 2^22 →
      heap node = combine compress (heap (2*node)) (heap (2*node+1)))
    (salt : Digest) (value : Entry) (index : Nat) (inside : index < 2^24)
    (group : heap (2^22+index/4) = s6GroupValues permutation leaf (index/4))
    (own : leaf index = s3LeafDigest permutation salt value) :
    s6RecordRoot compress permutation salt value index (fun k => leaf (s6OtherLeaf index k.val))
      (s6Sibling heap index) = heap (256+index/2^16) := by
  rw [s6RecordRoot, s6_record_group_honest permutation leaf salt value index own, ← group,
    s6_record_path_heap heap index inside,
    reconstruct_heap_ancestor compress heap (2^22) parents 14 (2^22+index/4)
      (by omega) (by omega)]
  congr 1
  omega

theorem s6_record_root_honest (compress : Compression) (permutation : Perm) (message : Message)
    (salt : Index → Digest) (index : Index) :
    s6RecordRoot (s6Compress compress) permutation (salt index) (message index) index.val
      (fun k => s6LeafValues permutation message salt (s6OtherLeaf index.val k.val))
      (s6Sibling (s6Heap compress permutation message salt) index.val) =
      s6Heap compress permutation message salt (256+index.val/2^16) := by
  have inside : index.val < 2^24 := index.isLt
  exact s6_record_root_heap (s6Compress compress) permutation _ _
    (fun node positive below => s6_heap_parent compress permutation message salt node positive below)
    (salt index) (message index) index.val inside
    (s6_heap_group compress permutation message salt (index.val/4) (by omega))
    (s6_leaf_values_index permutation message salt index)

end CommitGolfCandidate
