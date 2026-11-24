import CommitGolfCandidate.ChainedCachedFooter
import CommitGolfCandidate.TwoPermutationPackedOpeningModel

/-! The actual serialized chained commitment determines canonical raw packet fields. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 8192

theorem cached_sibling_positive (index : Index) (level : Nat) (inside : level<16) :
    0<(lowerNode index level ^^^ 1) := by
  have divisor : 0<2^level := by positivity
  have power : 2^level≤65536 := Nat.pow_le_pow_right (by decide) (by omega : level≤16)
  have big : 2≤lowerNode index level := by
    apply (Nat.le_div_iff_mul_le divisor).mpr
    change 2*2^level≤16777216+index.val
    omega
  by_cases even : lowerNode index level%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

theorem cached_frontier_positive (groups : List Nat) (node height : Nat) (span : CapSpan node height) :
    ∀ n ∈ capFrontierNodes groups node height, 0<n := by
  induction height generalizing node with
  | zero =>
    have bound := (cap_span_node node 0 span).1
    cases marked : capIsMarked groups node 0 <;> simp [capFrontierNodes,marked] <;> omega
  | succ height ih =>
    have children := cap_span_children node height span
    have bound := (cap_span_node node (height+1) span).1
    cases marked : capIsMarked groups node (height+1)
    · simp only [capFrontierNodes,marked,Bool.false_eq_true,ite_false,List.mem_singleton]
      intro n same
      subst n
      omega
    · intro n member
      simp only [capFrontierNodes,marked,Bool.true_eq,ite_true,List.mem_append] at member
      exact member.elim (ih _ children.1 n) (ih _ children.2 n)

theorem cached_opening_node_domain (positions : Positions) (node : Nat) (member : node∈openingNodes positions) :
    0<node ∧ node<512 := by
  by_cases empty : positions.card=0
  · simp [openingNodes,empty] at member
  · have live : node∈capFrontierNodes (groupsBefore positions positions.card) 1 8 := by
      simpa only [openingNodes,ite_eq_right empty] using member
    exact ⟨cached_frontier_positive _ _ _ cap_span_root _ live,
      cap_frontier_nodes_small _ _ _ cap_span_root _ live⟩

def cachedRecords (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions) : List InteriorCodec.Record :=
  (positions.sort (·≤·)).map fun index => cachedRecord heap (salts index) index

theorem cached_records_count (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions) :
    (cachedRecords heap salts positions).length=positions.card := by simp [cachedRecords]

theorem serialized_cached_packet (candidate : Submission) (trapdoor : BitVec (8*candidate.sizes.trapdoor))
    (oracle : Oracle) (leaves : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions)
    (heap : ∀ node, 0<node → node<2*LENGTH → trapdoorHeap (s := candidate) trapdoor node=
      (referenceHeap oracle leaves node).setWidth 256)
    (nonces : ∀ index, trapdoorSalt (s := candidate) trapdoor index=salts index)
    (masked : ∀ index, (salts index).toNat<2^121) :
    rawRecordStream (cachedRecords (referenceHeap oracle leaves) salts positions)++
      rawFieldsBytes (footerRawFields (openingNodes positions)
        (cachedFooter (openingNodes positions) (referenceHeap oracle leaves)))=
      TwoPermutationPrototype.PackedOpening.proofFromTrapdoor (s := candidate) trapdoor positions := by
  unfold rawRecordStream cachedRecords TwoPermutationPrototype.PackedOpening.proofFromTrapdoor
  rw [List.flatMap_map,cached_footer_raw_bytes oracle leaves _ (fun node member =>
    (cached_opening_node_domain positions node member).2)]
  congr 1
  · apply List.flatMap_congr
    intro index member
    rw [cached_record_raw_bytes oracle leaves _ _ (masked index),cached_record_source,nonces]
    unfold lowerRecord
    congr 1
    apply List.flatMap_congr
    intro level member
    exact congrArg (proofDigestBytes (true && level != 0))
      (heap _ (cached_sibling_positive index level (List.mem_range.mp member)) (lower_swap_bound index level)).symm
  · apply List.flatMap_congr
    intro node member
    rw [heap _ (cached_opening_node_domain positions node member).1
      ((cached_opening_node_domain positions node member).2.trans_le (by decide : 512≤2*LENGTH))]

theorem delivered_cached_packet (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    rawRecordStream (cachedRecords heap (deliveredSalts oracle key) positions)++
      rawFieldsBytes (footerRawFields (openingNodes positions) (cachedFooter (openingNodes positions) heap))=
      TwoPermutationPrototype.PackedOpening.proofFromTrapdoor (s := Artifact.submission) trapdoor positions := by
  exact serialized_cached_packet Artifact.submission _ oracle _ _ positions
    (delivered_physical_results oracle message key).2.1 (delivered_physical_results oracle message key).2.2
    (delivered_salt_width oracle key)

end CommitGolfCandidate.Chained.Native
