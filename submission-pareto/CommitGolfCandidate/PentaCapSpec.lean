import CommitGolfCandidate.TwoPermutationPentaSpec

/-! Level-13 cap penta proofs (penta4 + binary hybrid tree).

Each record keeps the salt, the four other slots of the 5-ary levels 0-2 and one sibling per
binary level 3-13 (752 bytes). When at least one position is opened a table of the 66 level-14
nodes follows; the checker recomputes levels 15-21 from it. The table is a function of the node
table of the tree, so the builder reads the node function only on honest inputs. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

/-- Position `o` of the sorted positions (0 past the end). -/
def sortedIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

theorem sorted_index_small (positions : Positions) (o : Nat) : sortedIndex positions o < 16777216 := by
  unfold sortedIndex
  cases h : (positions.sort (· ≤ ·))[o]? with
  | none => simp
  | some x =>
    have hx : x.val < 16777216 := x.isLt
    simpa using hx

/-- The table level: records carry levels below it, the proof ends with every level-14 node. -/
def CAP_LEVEL : Nat := 13

theorem cap_count_value : pentaCount CAP_LEVEL = 53 := by decide

/-- The other child of a binary group, by slot. -/
def binSibling (index : Index) (k : Nat) : Fin 5 :=
  ⟨3 + (1 - index.val / placeValue k % 2), by omega⟩

/-- A record: the salt, the four other slots of the record's group at the 5-ary levels
`0 … PENTA_LOW - 1` (rotation order), then the sibling at each binary level below `CAP_LEVEL`
(16 + 3 · 128 + 11 · 32 = 752 bytes). -/
def capRecord (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    List Byte :=
  saltBytes salt ++
  ((List.range PENTA_LOW).flatMap fun k =>
    (List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))) ++
  ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
    digestBytes (pentaGroup penta leaves (PENTA_LOW + m) (index.val / placeValue (PENTA_LOW + m + 1))
      (binSibling index (PENTA_LOW + m))))

/-- Every node of level `k`, in order. -/
def capLevel (penta : PentaFunction) (leaves : DigestTape) (k : Nat) : List Byte :=
  (List.range (pentaCount k)).flatMap fun j => digestBytes (pentaNode penta leaves k j)

theorem cap_record_length (penta : PentaFunction) (leaves : DigestTape) (index : Index)
    (salt : BitVec 128) : (capRecord penta leaves index salt).length = 816 := by
  have inner : ∀ k, ((List.range 4).flatMap fun j =>
      digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))).length = 128 := by
    intro k
    simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]
  unfold capRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, inner, digestBytes, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul, PENTA_LOW, CAP_LEVEL]

theorem cap_level_length (penta : PentaFunction) (leaves : DigestTape) (k : Nat) :
    (capLevel penta leaves k).length = 32 * pentaCount k := by
  unfold capLevel
  simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

/-- The submitted format: records in ascending position order, then every level-14 node
(2,112 bytes); the checker recomputes levels 15 to 21. An empty opening has no table. -/
def capTranscriptBuilder : PentaTranscriptBuilder :=
  fun penta positions salts leaves =>
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    (pentaRoot penta leaves,
      ordered.flatMap (fun index => capRecord penta leaves index.val (salts index)) ++
        (if positions.card = 0 then [] else capLevel penta leaves CAP_LEVEL))

def capLength (positions : Positions) : Nat :=
  816 * positions.card + (if positions.card = 0 then 0 else 1696)

theorem cap_proof_length (penta : PentaFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    (capTranscriptBuilder penta positions salts leaves).2.length = capLength positions := by
  simp only [capTranscriptBuilder, List.length_append, List.length_flatMap, cap_record_length,
    List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_sort, Finset.card_attach, capLength]
  split <;> simp [cap_level_length, cap_count_value, Nat.mul_comm]

theorem cap_transcript_builder_local : PentaBuildLocal capTranscriptBuilder := by
  intro penta penta' positions salts leaves same
  have nodes := penta_node_congr penta penta' leaves same
  have groups : ∀ k, k ≤ PENTA_LEVELS → ∀ g, pentaGroup penta leaves k g = pentaGroup penta' leaves k g :=
    fun k hk g => penta_group_of_nodes _ _ _ k g (nodes k hk)
  have root : pentaRoot penta leaves = pentaRoot penta' leaves := nodes _ le_rfl _
  have record : ∀ index salt, capRecord penta leaves index salt = capRecord penta' leaves index salt := by
    intro index salt
    unfold capRecord
    have a : ((List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaGroup penta leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))) =
      ((List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaGroup penta' leaves k (index.val / placeValue (k + 1)) (pentaRot index k j))) := by
      apply List.flatMap_congr
      intro k member
      have : k < 4 := List.mem_range.mp member
      rw [groups k (by unfold PENTA_LEVELS; omega)]
    have b : ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
        digestBytes (pentaGroup penta leaves (PENTA_LOW + m) (index.val / placeValue (PENTA_LOW + m + 1))
          (binSibling index (PENTA_LOW + m)))) =
      ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
        digestBytes (pentaGroup penta' leaves (PENTA_LOW + m) (index.val / placeValue (PENTA_LOW + m + 1))
          (binSibling index (PENTA_LOW + m)))) := by
      apply List.flatMap_congr
      intro m member
      have : m < 9 := List.mem_range.mp member
      rw [groups (PENTA_LOW + m) (by unfold PENTA_LEVELS PENTA_LOW; omega)]
    rw [a, b]
  have table : capLevel penta leaves CAP_LEVEL = capLevel penta' leaves CAP_LEVEL := by
    unfold capLevel
    apply List.flatMap_congr
    intro j _
    rw [nodes CAP_LEVEL (by decide)]
  simp only [capTranscriptBuilder, root, record, table]

end TwoPermutationPrototype.Sampling
