import CommitGolf.Programs
import CommitGolfCandidate.S6Tree

/-! Proof codec between the opener's internal proof and the delivered proof.

Internal record (576 bytes): salt field (nonce 16, tag 8, zero 8), the three other leaf digests of
the group (96), 14 path siblings of 32 bytes. The first sibling is a group digest; the other 13 are
internal nodes, which keep all 256 bits of their compression reply. The footer holds 32-byte
cap-level nodes.

Packed record (560 bytes): nonce, the three digests and the first sibling, then the 13 internal
siblings, all 32 bytes. Footer nodes are copied whole.

Expansion rebuilds the tag and the eight zero bytes of the salt field from the record's position
(records follow the positions in increasing order). -/
namespace CommitGolfCandidate
open CommitGolf

/-- Internal record (576 bytes) -> packed record (560 bytes). -/
def s6PackRecord (record : List Byte) : List Byte :=
  record.take 16 ++ (record.drop 32).take 128 ++
    (List.range 13).flatMap fun j => ((record.drop (160 + 32 * j)).take 32)

/-- A 32-byte node, copied whole. -/
def s6PackNode (node : List Byte) : List Byte := node.take 32

/-- `nodes` consecutive 32-byte nodes, each copied whole. -/
def s6PackNodes : Nat → List Byte → List Byte
  | 0, _ => []
  | nodes + 1, bytes => s6PackNode bytes ++ s6PackNodes nodes (bytes.drop 32)

/-- `count` records, then the footer: every remaining whole 32-byte node. -/
def s6Pack : Nat → List Byte → List Byte
  | 0, proof => s6PackNodes (proof.length / 32) proof
  | count + 1, proof => s6PackRecord proof ++ s6Pack count (proof.drop 576)

/-- The tag of a position as 8 little-endian bytes. -/
def s6TagBytes (index : Index) : List Byte :=
  (List.range 8).map fun byte => BitVec.ofNat 8 (s6Tag index / 2 ^ (8 * byte))

/-- `nodes` consecutive 32-byte fields, copied whole. -/
def s6ExpandNodes : Nat → List Byte → List Byte
  | 0, _ => []
  | nodes + 1, bytes => bytes.take 32 ++ s6ExpandNodes nodes (bytes.drop 32)

/-- Packed record of the leaf `index` -> internal record. -/
def s6ExpandRecord (index : Index) (packed : List Byte) : List Byte :=
  packed.take 16 ++ s6TagBytes index ++ List.replicate 8 0 ++ (packed.drop 16).take 128 ++
    s6ExpandNodes 13 (packed.drop 144)

/-- One packed record per listed position, then every remaining whole 32-byte footer field. -/
def s6ExpandRecords : List Index → List Byte → List Byte
  | [], proof => s6ExpandNodes (proof.length / 32) proof
  | index :: rest, proof => s6ExpandRecord index proof ++ s6ExpandRecords rest (proof.drop 560)

/-- Expansion of a delivered proof: `none` unless it holds 560 bytes per position and whole
32-byte footer fields. Record `r` belongs to the `r`-th position in increasing order. -/
def s6Expand (positions : Positions) (proof : List Byte) : Option (List Byte) :=
  if 560 * positions.card ≤ proof.length ∧ (proof.length - 560 * positions.card) % 32 = 0 then
    some (s6ExpandRecords (positions.sort (· ≤ ·)) proof)
  else none

/-- `nodes` consecutive 32-byte nodes. Full-width nodes carry no redundant bytes, so the
condition is vacuous; it is kept so that the record and proof predicates keep their shape. -/
def S6NodesCanonical : Nat → List Byte → Prop
  | 0, _ => True
  | nodes + 1, bytes => S6NodesCanonical nodes (bytes.drop 32)

theorem s6_nodes_canonical (nodes : Nat) (bytes : List Byte) : S6NodesCanonical nodes bytes := by
  induction nodes generalizing bytes with
  | zero => trivial
  | succ nodes ih => exact ih _

/-- An internal record of the leaf `index`: its tag at bytes 16..24 and zero bytes 24..32. -/
def S6RecordCanonical (index : Index) (record : List Byte) : Prop :=
  (record.drop 16).take 8 = s6TagBytes index ∧ (record.drop 24).take 8 = List.replicate 8 0 ∧
    S6NodesCanonical 13 (record.drop 160)

/-- One canonical 576-byte record per listed position, then whole 32-byte footer nodes. -/
def S6RecordsCanonical : List Index → List Byte → Prop
  | [], proof => proof.length % 32 = 0 ∧ S6NodesCanonical (proof.length / 32) proof
  | index :: rest, proof =>
      576 ≤ proof.length ∧ S6RecordCanonical index proof ∧ S6RecordsCanonical rest (proof.drop 576)

/-- The internal proofs the codec restores exactly. -/
def S6Canonical (positions : Positions) (proof : List Byte) : Prop :=
  S6RecordsCanonical (positions.sort (· ≤ ·)) proof

/-! ### Lengths and source offsets of packing -/

/-- Source offset of packed node byte `k`. -/
def s6NodeSource (k : Nat) : Nat := 32 * (k / 32) + k % 32

/-- Source offset of packed record byte `k < 560`. -/
def s6RecordSource (k : Nat) : Nat :=
  if k < 16 then k else if k < 144 then k + 16 else 160 + s6NodeSource (k - 144)

/-- Source offset of byte `k` of `s6Pack count`. -/
def s6PackSource : Nat → Nat → Nat
  | 0, k => s6NodeSource k
  | count + 1, k => if k < 560 then s6RecordSource k else 576 + s6PackSource count (k - 560)

theorem s6_pack_nodes_flatMap (nodes start : Nat) (bytes : List Byte) :
    ((List.range nodes).flatMap fun j => ((bytes.drop (start + 32 * j)).take 32)) =
      s6PackNodes nodes (bytes.drop start) := by
  induction nodes generalizing start with
  | zero => rfl
  | succ nodes ih =>
    have tail : (bytes.drop start).drop 32 = bytes.drop (start + 32) := by
      rw [List.drop_drop]
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, s6PackNodes, tail,
      ← ih (start + 32)]
    congr 1
    all_goals first
      | (simp only [s6PackNode, Nat.mul_zero, Nat.add_zero]; done)
      | (congr 1; funext j; congr 2; omega)

theorem s6_pack_record_nodes (record : List Byte) :
    s6PackRecord record = record.take 16 ++ (record.drop 32).take 128 ++
      s6PackNodes 13 (record.drop 160) := by
  rw [s6PackRecord, s6_pack_nodes_flatMap]

theorem s6_pack_nodes_length (nodes : Nat) (bytes : List Byte) (enough : 32 * nodes ≤ bytes.length) :
    (s6PackNodes nodes bytes).length = 32 * nodes := by
  induction nodes generalizing bytes with
  | zero => rfl
  | succ nodes ih =>
    rw [s6PackNodes, List.length_append, ih _ (by simp only [List.length_drop]; omega)]
    simp only [s6PackNode, List.length_take]
    omega

theorem s6_pack_record_length (record : List Byte) (enough : 576 ≤ record.length) :
    (s6PackRecord record).length = 560 := by
  rw [s6_pack_record_nodes]
  simp only [List.length_append, List.length_take, List.length_drop]
  rw [s6_pack_nodes_length 13 _ (by simp only [List.length_drop]; omega)]
  omega

theorem s6_pack_length (count nodes : Nat) (proof : List Byte)
    (size : proof.length = 576 * count + 32 * nodes) :
    (s6Pack count proof).length = 560 * count + 32 * nodes := by
  induction count generalizing proof with
  | zero =>
    rw [s6Pack, s6_pack_nodes_length _ _ (by omega)]
    omega
  | succ count ih =>
    rw [s6Pack, List.length_append, s6_pack_record_length _ (by omega),
      ih _ (by simp only [List.length_drop]; omega)]
    omega

theorem s6_pack_nodes_getElem? (nodes : Nat) (bytes : List Byte) (k : Nat) (inside : k < 32 * nodes)
    (enough : 32 * nodes ≤ bytes.length) :
    (s6PackNodes nodes bytes)[k]? = bytes[s6NodeSource k]? := by
  induction nodes generalizing bytes k with
  | zero => omega
  | succ nodes ih =>
    have first : (s6PackNode bytes).length = 32 := by
      simp only [s6PackNode, List.length_take]
      omega
    rw [s6PackNodes]
    by_cases low : k < 32
    · rw [List.getElem?_append_left (by omega)]
      simp only [s6PackNode, List.getElem?_take, if_pos low, s6NodeSource]
      congr 1
      omega
    · rw [List.getElem?_append_right (by omega), first,
        ih _ _ (by omega) (by simp only [List.length_drop]; omega), List.getElem?_drop]
      congr 1
      simp only [s6NodeSource]
      omega

theorem s6_pack_record_getElem? (record : List Byte) (k : Nat) (inside : k < 560)
    (enough : 576 ≤ record.length) :
    (s6PackRecord record)[k]? = record[s6RecordSource k]? := by
  rw [s6_pack_record_nodes]
  have headLength : (record.take 16).length = 16 := by simp only [List.length_take]; omega
  have middleLength : ((record.drop 32).take 128).length = 128 := by
    simp only [List.length_take, List.length_drop]; omega
  by_cases head : k < 16
  · rw [List.append_assoc, List.getElem?_append_left (by omega)]
    simp only [List.getElem?_take, if_pos head, s6RecordSource]
  · by_cases middle : k < 144
    · rw [List.append_assoc, List.getElem?_append_right (by omega), headLength,
        List.getElem?_append_left (by omega)]
      simp only [List.getElem?_take, if_pos (by omega : k - 16 < 128), List.getElem?_drop,
        s6RecordSource, if_neg head, if_pos middle]
      congr 1
      omega
    · rw [List.append_assoc, List.getElem?_append_right (by omega), headLength,
        List.getElem?_append_right (by omega), middleLength,
        s6_pack_nodes_getElem? 13 _ _ (by omega) (by simp only [List.length_drop]; omega),
        List.getElem?_drop]
      simp only [s6RecordSource, if_neg head, if_neg middle]
      rw [show k - 16 - 128 = k - 144 by omega]

theorem s6_pack_getElem? (count nodes : Nat) (proof : List Byte)
    (size : proof.length = 576 * count + 32 * nodes) (k : Nat) (inside : k < 560 * count + 32 * nodes) :
    (s6Pack count proof)[k]? = proof[s6PackSource count k]? := by
  induction count generalizing proof k with
  | zero =>
    have quotient : proof.length / 32 = nodes := by omega
    rw [s6Pack, quotient, s6_pack_nodes_getElem? _ _ _ (by omega) (by omega)]
    rfl
  | succ count ih =>
    rw [s6Pack]
    by_cases first : k < 560
    · rw [List.getElem?_append_left (by rw [s6_pack_record_length _ (by omega)]; exact first),
        s6_pack_record_getElem? _ _ first (by omega)]
      simp only [s6PackSource, if_pos first]
    · rw [List.getElem?_append_right (by rw [s6_pack_record_length _ (by omega)]; omega),
        s6_pack_record_length _ (by omega),
        ih _ (by simp only [List.length_drop]; omega) _ (by omega), List.getElem?_drop]
      simp only [s6PackSource, if_neg first]

/-- Source offsets of whole records and of the footer in `s6Pack`. -/
theorem s6_pack_source_record (count record k : Nat) (present : record < count) (inside : k < 560) :
    s6PackSource count (560 * record + k) = 576 * record + s6RecordSource k := by
  induction count generalizing record with
  | zero => omega
  | succ count ih =>
    rcases record with _ | record
    · simp only [s6PackSource, Nat.mul_zero, Nat.zero_add, if_pos inside]
    · have above : ¬ 560 * (record + 1) + k < 560 := by omega
      have shifted : 560 * (record + 1) + k - 560 = 560 * record + k := by omega
      simp only [s6PackSource, if_neg above, shifted, ih record (by omega)]
      omega

theorem s6_pack_source_footer (count k : Nat) :
    s6PackSource count (560 * count + k) = 576 * count + s6NodeSource k := by
  induction count with
  | zero => simp only [s6PackSource, Nat.mul_zero, Nat.zero_add]
  | succ count ih =>
    have above : ¬ 560 * (count + 1) + k < 560 := by omega
    have shifted : 560 * (count + 1) + k - 560 = 560 * count + k := by omega
    simp only [s6PackSource, if_neg above, shifted, ih]
    omega

/-! ### Round trip -/

theorem s6_expand_nodes_pack (nodes : Nat) (bytes tail : List Byte)
    (enough : 32 * nodes ≤ bytes.length) (canonical : S6NodesCanonical nodes bytes) :
    s6ExpandNodes nodes (s6PackNodes nodes bytes ++ tail) = bytes.take (32 * nodes) := by
  induction nodes generalizing bytes with
  | zero => rfl
  | succ nodes ih =>
    have firstLength : (s6PackNode bytes).length = 32 := by
      simp only [s6PackNode, List.length_take]
      omega
    rw [s6PackNodes, List.append_assoc, s6ExpandNodes,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
      List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
      ih _ (by simp only [List.length_drop]; omega) canonical]
    rw [show 32 * (nodes + 1) = 32 + 32 * nodes by omega, List.take_add]
    simp only [s6PackNode]

theorem s6_expand_record_pack (index : Index) (record tail : List Byte)
    (enough : 576 ≤ record.length) (canonical : S6RecordCanonical index record) :
    s6ExpandRecord index (s6PackRecord record ++ tail) = record.take 576 := by
  have headLength : (record.take 16).length = 16 := by simp only [List.length_take]; omega
  have middleLength : ((record.drop 32).take 128).length = 128 := by
    simp only [List.length_take, List.length_drop]; omega
  have frontLength : (record.take 16 ++ (record.drop 32).take 128).length = 144 := by
    rw [List.length_append, headLength, middleLength]
  rw [s6_pack_record_nodes, s6ExpandRecord]
  have regroup : record.take 16 ++ (record.drop 32).take 128 ++ s6PackNodes 13 (record.drop 160) ++ tail =
      record.take 16 ++ ((record.drop 32).take 128 ++ (s6PackNodes 13 (record.drop 160) ++ tail)) := by
    simp only [List.append_assoc]
  have regroup' : record.take 16 ++ (record.drop 32).take 128 ++ s6PackNodes 13 (record.drop 160) ++ tail =
      (record.take 16 ++ (record.drop 32).take 128) ++ (s6PackNodes 13 (record.drop 160) ++ tail) := by
    simp only [List.append_assoc]
  have head : (record.take 16 ++ (record.drop 32).take 128 ++ s6PackNodes 13 (record.drop 160) ++ tail).take 16 =
      record.take 16 := by
    rw [regroup]
    exact List.take_left' headLength
  have middle : ((record.take 16 ++ (record.drop 32).take 128 ++ s6PackNodes 13 (record.drop 160) ++ tail).drop 16).take 128 =
      (record.drop 32).take 128 := by
    rw [regroup, List.drop_left' headLength]
    exact List.take_left' middleLength
  have siblings : (record.take 16 ++ (record.drop 32).take 128 ++ s6PackNodes 13 (record.drop 160) ++ tail).drop 144 =
      s6PackNodes 13 (record.drop 160) ++ tail := by
    rw [regroup']
    exact List.drop_left' frontLength
  rw [head, middle, siblings,
    s6_expand_nodes_pack 13 _ _ (by simp only [List.length_drop]; omega) canonical.2.2,
    ← canonical.1, ← canonical.2.1]
  rw [show 576 = 16 + (8 + (8 + (128 + 32 * 13))) by rfl, List.take_add, List.take_add, List.take_add,
    List.take_add]
  simp only [List.drop_drop, List.append_assoc]
  try rfl

theorem s6_expand_records_pack (indices : List Index) (proof : List Byte)
    (canonical : S6RecordsCanonical indices proof) :
    s6ExpandRecords indices (s6Pack indices.length proof) = proof := by
  induction indices generalizing proof with
  | nil =>
    obtain ⟨whole, nodes⟩ := canonical
    have size : proof.length = 576 * 0 + 32 * (proof.length / 32) := by omega
    have packedLength := s6_pack_length 0 (proof.length / 32) proof size
    simp only [List.length_nil, s6ExpandRecords]
    rw [packedLength, show (560 * 0 + 32 * (proof.length / 32)) / 32 = proof.length / 32 by omega]
    have expanded := s6_expand_nodes_pack (proof.length / 32) proof [] (by omega) nodes
    rw [List.append_nil] at expanded
    rw [s6Pack, expanded, List.take_of_length_le (by omega)]
  | cons index rest ih =>
    obtain ⟨enough, record, tail⟩ := canonical
    simp only [List.length_cons, s6Pack, s6ExpandRecords]
    rw [s6_expand_record_pack index proof _ enough record,
      List.drop_left' (s6_pack_record_length _ enough), ih _ tail]
    exact List.take_append_drop 576 proof

theorem s6_records_canonical_length (indices : List Index) (proof : List Byte)
    (canonical : S6RecordsCanonical indices proof) :
    ∃ nodes, proof.length = 576 * indices.length + 32 * nodes := by
  induction indices generalizing proof with
  | nil => exact ⟨proof.length / 32, by have := canonical.1; simp only [List.length_nil]; omega⟩
  | cons index rest ih =>
    obtain ⟨nodes, size⟩ := ih _ canonical.2.2
    refine ⟨nodes, ?_⟩
    simp only [List.length_drop] at size
    have := canonical.1
    simp only [List.length_cons]
    omega

/-- Expansion inverts packing on every canonical internal proof. -/
theorem s6_expand_pack (positions : Positions) (proof : List Byte)
    (canonical : S6Canonical positions proof) :
    s6Expand positions (s6Pack positions.card proof) = some proof := by
  have sorted : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  obtain ⟨nodes, size⟩ := s6_records_canonical_length _ proof canonical
  rw [sorted] at size
  have packedLength := s6_pack_length positions.card nodes proof size
  rw [s6Expand, if_pos (by rw [packedLength]; omega)]
  congr 1
  have expanded := s6_expand_records_pack _ proof canonical
  rwa [sorted] at expanded

end CommitGolfCandidate
