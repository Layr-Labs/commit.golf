import CommitGolfCandidate.CapHonestLowerBytes
import CommitGolfCandidate.CapOpenLoadedBytes
import CommitGolfCandidate.S6Opening

/-! The bytes the cap-level opener emits for a committed state are the cap-level reference proof
of the committed tree: the eighteen-digest records of the requested positions in increasing
position order (tagged salt, the three other leaf digests of the group, fourteen siblings of the
group node), followed by the cap footer. Every slot is read from the committed state and
identified through `CommittedState`; no hash property is assumed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

/-- Every lower sibling read by a record is a heap node of the committed tree. -/
private theorem honest_sibling_bounds (index : Index) (level : Nat) (inside : level < 14) :
    0 < ((4194304+index.val/4)/2^level) ^^^ 1 ∧ ((4194304+index.val/4)/2^level) ^^^ 1 < 2^23 := by
  have bounded : index.val < 16777216 := index.isLt
  have powerPositive : 0 < 2^level := by positivity
  have powerBound : 2^(level+1) ≤ 2^14 := Nat.pow_le_pow_right (by decide) (by omega)
  have doubled : 2^(level+1) = 2*2^level := by rw [Nat.pow_succ]; omega
  have fourteen : (2 : Nat)^14 = 16384 := by norm_num
  rw [doubled, fourteen] at powerBound
  have lower : 2 ≤ (4194304+index.val/4)/2^level :=
    (Nat.le_div_iff_mul_le powerPositive).mpr (by omega)
  have upper : (4194304+index.val/4)/2^level < 2*4194304 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have sibling := heap_sibling_bounds 4194304 _ lower upper
  exact ⟨sibling.1, lt_of_lt_of_eq sibling.2 (by norm_num)⟩

/-- The honest record of `index` is the reference opening record of the committed tree. -/
theorem cap_honest_record_reference (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (index : Index) :
    capLowerEncoding (capHonestLowerRecord message committed index) =
      s6OpeningRecord
        (s6Heap oracle.compression oracle.permutation message
          (expandTaggedVector (committedNonce committed)))
        (s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed)))
        (expandTaggedVector (committedNonce committed)) index := by
  have bounded : index.val < 16777216 := index.isLt
  have others : (capHonestLowerRecord message committed index).others = fun k : Fin 3 =>
      s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed))
        (s6OtherLeaf index.val k.val) := by
    funext k
    have small : capOpenPlace index.val (k.val+1) < 4 := by
      unfold capOpenPlace
      split <;> omega
    have place : s6OtherLeaf index.val k.val =
        4*(index.val/4)+capOpenPlace index.val (k.val+1) := by
      simp only [s6OtherLeaf, capOpenPlace, Nat.add_sub_cancel]
    rw [place]
    exact cap_honest_cell_digest oracle message committed correct (index.val/4) _ small
      (by change _ < 16777216; omega)
  have siblings : (capHonestLowerRecord message committed index).sibling =
      s6Sibling (s6Heap oracle.compression oracle.permutation message
        (expandTaggedVector (committedNonce committed))) index.val := by
    funext level
    have node := honest_sibling_bounds index level.val level.isLt
    change heapDigest committed 4294971424 (((4194304+index.val/4)/2^level.val) ^^^ 1) =
      s6Heap oracle.compression oracle.permutation message
        (expandTaggedVector (committedNonce committed)) (((4194304+index.val/4)/2^level.val) ^^^ 1)
    exact correct.2.1 _ node.1 node.2
  rw [capLowerEncoding, s6OpeningRecord, List.cons_append, others, siblings]
  rfl

/-- The loaded lower records of a committed state are the reference opening records. -/
theorem cap_honest_lower_reference (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    capDigestEncoding (capLowerTranscript (capHonestLowerRecords message committed positions)) =
      referenceOpening
        (s6Heap oracle.compression oracle.permutation message
          (expandTaggedVector (committedNonce committed)))
        (s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed)))
        (expandTaggedVector (committedNonce committed)) positions := by
  have records : ∀ indices : List Index,
      (indices.map (capHonestLowerRecord message committed)).flatMap capLowerEncoding =
        indices.flatMap (s6OpeningRecord
          (s6Heap oracle.compression oracle.permutation message
            (expandTaggedVector (committedNonce committed)))
          (s6LeafValues oracle.permutation message (expandTaggedVector (committedNonce committed)))
          (expandTaggedVector (committedNonce committed))) := by
    intro indices
    induction indices with
    | nil => rfl
    | cons index rest ih =>
        rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, ih,
          cap_honest_record_reference oracle message committed correct index]
  rw [capDigestEncoding, capLowerTranscript, capHonestLowerRecords, capOpenRequestedIndices,
    records, referenceOpening]

private theorem cap_heap_tree_congr (roots roots' : Nat → Digest) (height node : Nat)
    (agree : ∀ leaf, node*2^height ≤ leaf → leaf < (node+1)*2^height → roots leaf = roots' leaf) :
    capHeapTree roots height node = capHeapTree roots' height node := by
  induction height generalizing node with
  | zero =>
      simp only [capHeapTree, agree node (by simp) (by simp)]
  | succ height ih =>
      simp only [capHeapTree]
      have power : 2^(height+1) = 2*2^height := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [ih (2*node) ?_, ih (2*node+1) ?_]
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith

private theorem cap_heap_view_roots_congr (roots roots' : Nat → Digest) (marked : Nat → Bool)
    (height node : Nat)
    (agree : ∀ leaf, node*2^height ≤ leaf → leaf < (node+1)*2^height → roots leaf = roots' leaf) :
    capHeapView roots marked height node = capHeapView roots' marked height node := by
  induction height generalizing node with
  | zero =>
      simp only [capHeapView, agree node (by simp) (by simp)]
  | succ height ih =>
      simp only [capHeapView]
      have power : 2^(height+1) = 2*2^height := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [ih (2*node) ?_, ih (2*node+1) ?_]
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith
      · intro leaf lower upper
        apply agree leaf
        · rw [power]; nlinarith
        · rw [power]; nlinarith

/-- On the cap leaves, the opener's occupancy marks are the reference marks. -/
theorem cap_open_requested_marks_cap (positions : Positions) (node : Nat) (lower : 256 ≤ node) :
    capOpenRequestedMarks positions node = s6CapMarks positions node := by
  have count : positions.card = (capOpenRequestedIndices positions).length := by
    simp only [capOpenRequestedIndices, Finset.length_sort]
  rw [capOpenRequestedMarks, cap_tree_marks_leaf _ _ lower, count, s6CapMarks]
  apply Bool.eq_iff_iff.mpr
  rw [cap_open_marks_seen_full, decide_eq_true_iff]
  constructor
  · rintro ⟨index, member, same⟩
    exact ⟨index, (Finset.mem_sort _).mp member, same.symm⟩
  · rintro ⟨index, member, same⟩
    exact ⟨index, (Finset.mem_sort _).mpr member, same.symm⟩

/-- The footer read from a committed state is the reference cap footer. -/
theorem cap_honest_footer_reference (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    capProof (s6Compress oracle.compression) (capHeapTree (heapDigest committed 4294971424) 8 1)
        (capHeapView (heapDigest committed 4294971424) (capOpenRequestedMarks positions) 8 1) =
      s6CapFooter (s6Compress oracle.compression)
        (s6Heap oracle.compression oracle.permutation message
          (expandTaggedVector (committedNonce committed))) positions := by
  have agree : ∀ leaf, 1*2^8 ≤ leaf → leaf < (1+1)*2^8 →
      heapDigest committed 4294971424 leaf =
        s6Heap oracle.compression oracle.permutation message
          (expandTaggedVector (committedNonce committed)) leaf := by
    intro leaf lower upper
    norm_num at lower upper
    exact correct.2.1 leaf (by omega) (by norm_num; omega)
  rw [cap_heap_tree_congr _ _ 8 1 agree, cap_heap_view_roots_congr _ _ _ 8 1 agree]
  exact s6_cap_footer_marks _ _ positions _
    (fun node lower _ => cap_open_requested_marks_cap positions node lower)

/-- For a committed state and a nonempty request, the cap-level opener's bytes are the
cap-level reference proof of the committed tree under its tagged nonces. -/
theorem cap_honest_opening_transcript (oracle : Oracle) (message : Message) (committed : MachineState)
    (correct : CommittedState oracle message committed) (positions : Positions)
    (positive : 0 < positions.card) :
    capOpenLoadedBytes (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      (referenceTranscript oracle.compression oracle.permutation message
        (expandTaggedVector (committedNonce committed)) positions).2 := by
  have nonzero : positions.card ≠ 0 := Nat.pos_iff_ne_zero.mp positive
  rw [reference_transcript_proof]
  simp only [nonzero, ↓reduceIte]
  rw [capOpenLoadedBytes, cap_honest_lower_loaded_transcript message committed positions,
    cap_open_honest_boundary_digests oracle message committed correct positions,
    cap_honest_lower_reference oracle message committed correct positions,
    cap_honest_footer_reference oracle message committed correct positions, capDigestEncoding]

end CommitGolfCandidate
