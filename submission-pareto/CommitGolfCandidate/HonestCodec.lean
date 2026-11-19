import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolfCandidate.ProofCodec
import CommitGolfCandidate.HeadStreamFour

/-! The honest packed-mode transcript has the unpacked codec layout, and every stored
internal digest has byte 29 below 64. Given the record-head facts `HeadFacts` (opened salts
below 2^122, opened leaf siblings below 2^242; `head_facts_of_small_salts`), the codec round-trips it. -/
namespace TwoPermutationPrototype.Sampling.HonestCodec
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

theorem getElem?_flatMap_uniform {α : Type} (L : List α) (f : α → List Byte) (n : Nat)
    (uniform : ∀ a ∈ L, (f a).length = n) (r : Nat) (hr : r < L.length) (o : Nat) (ho : o < n) :
    (L.flatMap f)[n*r + o]? = (f L[r])[o]? := by
  induction L generalizing r with
  | nil => simp at hr
  | cons a rest ih =>
    have ha : (f a).length = n := uniform a (by simp)
    rw [List.flatMap_cons]
    cases r with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ r =>
      rw [List.getElem?_append_right (by rw [ha]; nlinarith), ha,
        show n*(r+1) + o - n = n*r + o by rw [Nat.mul_succ]; omega]
      simp only [List.getElem_cons_succ]
      exact ih (fun b hb => uniform b (by simp [hb])) r (by simp at hr; omega)

theorem internal_byte29 (x : BitVec 256) :
    ((digestBytes ((0#16) ++ CommitGolfCandidate.low240 x))[29]?.getD 0).toNat < 64 := by
  have key : ((((0#16) ++ CommitGolfCandidate.low240 x).extractLsb' (8*29) 8)).toNat < 64 := by
    have hy : (CommitGolfCandidate.lowBits 238 x : BitVec 238).toNat < 2^238 := BitVec.isLt _
    simp only [BitVec.extractLsb'_toNat, CommitGolfCandidate.low240, BitVec.toNat_append,
      BitVec.toNat_ofNat]
    simp
    omega
  simpa [digestBytes] using key

theorem heap_byte29 (compress : Compression) (leaves : DigestTape) (node : Nat)
    (lo : 0 < node) (hi : node < LENGTH) :
    ((digestBytes (transcriptHeap true compress leaves node))[29]?.getD 0).toNat < 64 := by
  rw [transcript_heap_parent true compress leaves node lo hi]
  simp only [projectInternal]
  exact internal_byte29 _

theorem lower_sibling_internal (index : Index) (level : Nat) (later : 0 < level) (within : level < 16) :
    0 < ((LENGTH + index.val) / 2^level) ^^^ 1 ∧ ((LENGTH + index.val) / 2^level) ^^^ 1 < LENGTH := by
  have bounded := index.isLt
  have scale : 2 ≤ (2:Nat)^level := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show 1 ≤ level by omega)
  have scaleBound : (2:Nat)^level ≤ 32768 :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show level ≤ 15 by omega)).trans (by decide)
  generalize hnode : (LENGTH + index.val) / 2^level = node
  have lo : 2 ≤ node := by
    rw [← hnode]
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < (2:Nat)^level)).mpr
    change 2*2^level ≤ 16777216+index.val
    omega
  have hi : node < LENGTH := by
    rw [← hnode]
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2:Nat)^level)).mpr
    have fit : (16777216:Nat)*2 ≤ 16777216*2^level := Nat.mul_le_mul_left _ scale
    change 16777216+index.val < 16777216*2^level
    change index.val < 16777216 at bounded
    omega
  change 0 < node ^^^ 1 ∧ node ^^^ 1 < 16777216
  change node < 16777216 at hi
  by_cases parity : node % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr parity)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

theorem frontier_nodes_range (groups : List Nat) (node height entry : Nat) (positive : 1 ≤ node)
    (member : entry ∈ capFrontierNodes groups node height) :
    node ≤ entry ∧ entry < (node+1) * 2^height := by
  induction height generalizing node with
  | zero =>
    unfold capFrontierNodes at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst member
      simp
  | succ height ih =>
    unfold capFrontierNodes at member
    split at member
    · rcases List.mem_append.mp member with child | child
      · have := ih _ (by omega) child
        rw [Nat.pow_succ]
        constructor
        · omega
        · nlinarith [this.2]
      · have := ih _ (by omega) child
        rw [Nat.pow_succ]
        constructor
        · omega
        · nlinarith [this.2]
    · rw [List.mem_singleton] at member
      subst member
      have : 1 ≤ 2^(height+1) := Nat.one_le_two_pow
      constructor <;> nlinarith

theorem lower_record_byte29 (compress : Compression) (leaves : DigestTape) (index : Index)
    (salt : BitVec 128) (d : Nat) (hd : d < 15) :
    ((lowerRecord true (transcriptHeap true compress leaves) index salt)[48 + 30*d + 29]?.getD 0).toNat < 64 := by
  unfold lowerRecord
  rw [List.getElem?_append_right (by simp [saltBytes])]
  simp only [saltBytes, List.length_ofFn]
  rw [List.range_succ_eq_map, List.flatMap_cons, List.getElem?_append_right (by
    simp [proofDigestBytes, digestBytes]; omega)]
  have h0 : (proofDigestBytes (true && (0 != 0)) (transcriptHeap true compress leaves
      (((LENGTH + index.val) / 2^0) ^^^ 1))).length = 32 := by
    simp [proofDigestBytes, digestBytes]
  rw [h0, show 48 + 30*d + 29 - 16 - 32 = 30*d + 29 by omega, List.flatMap_map]
  rw [getElem?_flatMap_uniform (List.range 15) _ 30 (by
      intro a _
      simp [proofDigestBytes, digestBytes]) d (by simp; omega) 29 (by decide)]
  have hc : (true && (d.succ != 0)) = true := by simp
  simp only [List.getElem_range, proofDigestBytes]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  rw [List.getElem?_take_of_lt (by decide)]
  obtain ⟨lo, hi⟩ := lower_sibling_internal index (d+1) (by omega) (by omega)
  exact heap_byte29 compress leaves _ lo hi

/-- Record-head facts of the honest transcript that codec v2 needs: every opened salt has
byte 15 below 4 (122-bit salts), and every opened record's leaf sibling has byte 30 below 4
and byte 31 zero (242-bit leaf digests). `head_facts_of_small_salts` derives them from
salts below `2^122`. -/
structure HeadFacts (compress : Compression) (positions : Positions) (salts : OpenedSalts positions)
    (leaves : DigestTape) : Prop where
  salt : ∀ index : {i : Index // i ∈ positions}, ((saltBytes (salts index))[15]?.getD 0).toNat < 4
  leaf : ∀ index : {i : Index // i ∈ positions},
    ((digestBytes (transcriptHeap true compress leaves ((LENGTH + index.val.val) ^^^ 1)))[30]?.getD 0).toNat < 4
  leafTop : ∀ index : {i : Index // i ∈ positions},
    (digestBytes (transcriptHeap true compress leaves ((LENGTH + index.val.val) ^^^ 1)))[31]?.getD 0 = 0

theorem lower_record_salt (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) :
    (lowerRecord true heap index salt)[15]? = (saltBytes salt)[15]? := by
  unfold lowerRecord
  rw [List.getElem?_append_left (by simp [saltBytes])]

theorem lower_record_leaf (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) (o : Nat) (ho : o < 32) :
    (lowerRecord true heap index salt)[16 + o]? = (digestBytes (heap ((LENGTH + index.val) ^^^ 1)))[o]? := by
  unfold lowerRecord
  rw [List.getElem?_append_right (by simp [saltBytes])]
  simp only [saltBytes, List.length_ofFn]
  rw [List.range_succ_eq_map, List.flatMap_cons, show 16 + o - 16 = o by omega,
    List.getElem?_append_left (by simp [proofDigestBytes, digestBytes]; omega)]
  simp [proofDigestBytes]

theorem honest_codec_shape (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    let proof := (transcriptBuilder true compress positions salts leaves).2
    ∃ b, proof.length = 498*positions.card + 30*b ∧ b ≤ 128 ∧
      (∀ j < 15*positions.card + b,
        (proof.getD (ProofCodec.unpackedDigest positions.card j + 29) 0).toNat < 64) ∧
      (HeadFacts compress positions salts leaves →
        (∀ r < positions.card, (proof.getD (498*r+15) 0).toNat < 4) ∧
        (∀ r < positions.card, (proof.getD (498*r+46) 0).toNat < 4) ∧
        (∀ r < positions.card, proof.getD (498*r+47) 0 = 0)) := by
  intro proof
  let heap := transcriptHeap true compress leaves
  let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
  let groups := ordered.map (capGroup ∘ Subtype.val)
  let path := ordered.flatMap (fun index => lowerRecord true heap index.val (salts index))
  let nodes := capFrontierNodes groups 1 8
  have hproof : proof = path ++ frontierProof true heap groups := rfl
  have hord : ordered.length = positions.card := by simp [ordered]
  have hrec : ∀ index ∈ ordered, (lowerRecord true heap index.val (salts index)).length = 498 := by
    intro index _
    simp [lower_record_length]
  have hpath : path.length = 498*positions.card := by
    simp only [path, List.length_flatMap]
    rw [List.map_congr_left (fun index h => hrec index h)]
    simp [hord, Nat.mul_comm]
  have hnodes : nodes.length ≤ 128 :=
    (cap_frontier_length groups 1 8).trans_le (production_boundary_bound (capMarkTree groups 1 8))
  have hfoot : ∀ node ∈ nodes, (proofDigestBytes true (heap node)).length = 30 := by
    intro node _
    simp [proof_digest_length]
  let b := if groups.isEmpty then 0 else nodes.length
  have hflen : (frontierProof true heap groups).length = 30*b := by
    unfold frontierProof
    simp only [b]
    split
    · simp
    · simp only [List.length_flatMap]
      rw [List.map_congr_left (fun node h => hfoot node h)]
      simp [nodes, Nat.mul_comm]
  have head : ∀ r (hr : r < ordered.length), ∀ o < 498, proof.getD (498*r+o) 0 =
      (lowerRecord true heap ordered[r].val (salts ordered[r]))[o]?.getD 0 := by
    intro r hr o ho
    rw [hproof, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hpath, ← hord]; nlinarith),
      getElem?_flatMap_uniform ordered _ 498 hrec r hr o ho]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · rw [hproof, List.length_append, hpath, hflen]
  · simp only [b]; split <;> omega
  swap
  · intro facts
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · rw [head r (by rw [hord]; omega) 15 (by decide), lower_record_salt]
      exact facts.salt _
    · rw [head r (by rw [hord]; omega) 46 (by decide), show 46 = 16 + 30 from rfl, lower_record_leaf _ _ _ 30 (by decide)]
      exact facts.leaf _
    · rw [head r (by rw [hord]; omega) 47 (by decide), show 47 = 16 + 31 from rfl, lower_record_leaf _ _ _ 31 (by decide)]
      exact facts.leafTop _
  intro j hj
  rw [hproof, List.getD_eq_getElem?_getD]
  unfold ProofCodec.unpackedDigest
  split
  · rename_i hjk
    rw [List.getElem?_append_left (by rw [hpath]; omega)]
    have e : 498*(j/15) + 48 + 30*(j%15) + 29 = 498*(j/15) + (48 + 30*(j%15) + 29) := by omega
    rw [e, getElem?_flatMap_uniform ordered _ 498 hrec (j/15) (by rw [hord]; omega) _ (by omega)]
    exact lower_record_byte29 compress leaves _ _ (j%15) (Nat.mod_lt _ (by decide))
  · rename_i hjk
    rw [List.getElem?_append_right (by rw [hpath]; omega), hpath]
    have e : 498*positions.card + 30*(j - 15*positions.card) + 29 - 498*positions.card =
        30*(j - 15*positions.card) + 29 := by omega
    rw [e]
    unfold frontierProof
    split
    · rename_i hempty
      simp only [b, hempty, ite_true] at hj
      omega
    · rename_i hne
      simp only [b, hne, Bool.false_eq_true, ite_false] at hj
      have hidx : j - 15*positions.card < nodes.length := by omega
      rw [getElem?_flatMap_uniform nodes _ 30 hfoot (j - 15*positions.card) hidx 29 (by decide)]
      simp only [proofDigestBytes, ite_true]
      rw [List.getElem?_take_of_lt (by decide)]
      have range := frontier_nodes_range groups 1 8 _ (le_refl 1) (List.getElem_mem hidx)
      exact heap_byte29 compress leaves _ (by omega) (by change _ < 16777216; omega)

private theorem leaf_sibling_node (i : Nat) (inside : i < LENGTH) :
    ∃ j, ∃ h : j < LENGTH, (LENGTH + i) ^^^ 1 = LENGTH + (⟨j, h⟩ : Index).val := by
  change i < 16777216 at inside
  rcases Nat.even_or_odd i with even | odd
  · have parity : (LENGTH + i) % 2 = 0 := by
      obtain ⟨k, hk⟩ := even; change (16777216 + i) % 2 = 0; omega
    refine ⟨i+1, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := even; change i+1 < 16777216; omega
    · rw [Nat.xor_one_of_even (Nat.even_iff.mpr parity)]; rfl
  · have parity : (LENGTH + i) % 2 = 1 := by
      obtain ⟨k, hk⟩ := odd; change (16777216 + i) % 2 = 1; omega
    refine ⟨i-1, by change i-1 < 16777216; omega, ?_⟩
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr parity)]
    obtain ⟨k, hk⟩ := odd
    change 16777216 + i - 1 = 16777216 + (i-1)
    omega

private theorem digest_byte (x : BitVec 256) (k : Nat) (hk : k < 32) :
    ((digestBytes x)[k]?.getD 0).toNat = x.toNat / 2^(8*k) % 2^8 := by
  simp only [digestBytes, List.getElem?_ofFn, hk, Option.getD_some]
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem salt_byte (x : BitVec 128) :
    ((saltBytes x)[15]?.getD 0).toNat = x.toNat / 2^(8*15) % 2^8 := by
  simp only [saltBytes, List.getElem?_ofFn, show 15 < 16 by decide, Option.getD_some]
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Opened salts below `2^122` and packed (242-bit) leaves give the record-head facts. -/
theorem head_facts_of_small_salts (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape)
    (small : ∀ index, (salts index).toNat < 2^122) : HeadFacts compress positions salts leaves := by
  have leafValue (index : {i : Index // i ∈ positions}) : ∃ v : Nat, v < 2^242 ∧
      (transcriptHeap true compress leaves ((LENGTH + index.val.val) ^^^ 1)).toNat = v := by
    obtain ⟨j, h, node⟩ := leaf_sibling_node index.val.val index.val.isLt
    rw [node, transcript_heap_leaf]
    refine ⟨(leaves ⟨j, h⟩).toNat % 2^242, Nat.mod_lt _ (by positivity), ?_⟩
    change (BitVec.ofNat 256 ((leaves ⟨j, h⟩).toNat % 2^242)).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num))
  refine ⟨fun index => ?_, fun index => ?_, fun index => ?_⟩
  · have h := small index
    rw [salt_byte]
    have q : (salts index).toNat / 2^(8*15) < 4 := by
      apply Nat.div_lt_of_lt_mul; norm_num; omega
    exact lt_of_le_of_lt (Nat.mod_le _ _) q
  · obtain ⟨v, hv, eq⟩ := leafValue index
    rw [digest_byte _ 30 (by decide), eq]
    have q : v / 2^(8*30) < 4 := by
      apply Nat.div_lt_of_lt_mul; norm_num; omega
    exact lt_of_le_of_lt (Nat.mod_le _ _) q
  · obtain ⟨v, hv, eq⟩ := leafValue index
    apply BitVec.eq_of_toNat_eq
    rw [digest_byte _ 31 (by decide), eq]
    have q : v / 2^(8*31) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hv (by norm_num))
    rw [q]
    rfl

theorem honest_unpack_pack (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (heads : HeadFacts compress positions salts leaves) :
    let proof := (transcriptBuilder true compress positions salts leaves).2
    ProofCodec.unpack positions.card (ProofCodec.pack positions.card proof) = some proof := by
  intro proof
  obtain ⟨b, len, hb, top, headBytes⟩ := honest_codec_shape compress positions salts leaves
  obtain ⟨salt, leaf, leafTop⟩ := headBytes heads
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  change positions.card ≤ 16777216 at card
  exact ProofCodec.unpack_pack positions.card b proof len
    (by unfold ProofCodec.packedLength ProofCodec.bodyLength; omega) top salt
    (fun r hr => lt_trans (leaf r hr) (by decide)) leafTop

end TwoPermutationPrototype.Sampling.HonestCodec

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

/-- The delivered transcript: the packed-mode commitment with the codec-packed proof. -/
def packedBuilder : TranscriptBuilder := fun compress positions salts leaves =>
  ((transcriptBuilder true compress positions salts leaves).1,
    ProofCodec.HeadStreamFour.pack positions.card (transcriptBuilder true compress positions salts leaves).2)

end TwoPermutationPrototype.Sampling
