import CommitGolfCandidate.TwoPermutationPentaSpec

/-! Level-7 cap penta proofs.

At 128 positions the top four levels of the donor's 1424-byte records repeat: levels 7, 8, 9 and 10
hold only 215 + 45 + 10 + 5 = 275 slots (`5 · pentaCount (k+1)` per level, ragged zero slots
included). A cap proof keeps the first 912 bytes of every record (the salt and the siblings of
levels `0 … 6`) and, when at least one position is opened, appends a table in trapdoor order, omitting the last three zero slots of level 10. The table is a function of the node table of the penta tree, so
the builder reads the node function only on honest inputs and is local like the penta builder. -/
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

/-- Slots of level `k`: every slot of its `pentaCount (k+1)` groups. -/
def capSlots (k : Nat) : Nat := 5 * pentaCount (k+1)

theorem cap_slots_values : capSlots 7 = 215 ∧ capSlots 8 = 45 ∧ capSlots 9 = 10 ∧ capSlots 10 = 5 := by
  decide

/-- A record without its top four levels: the salt and, for levels `0 … 6`, all five slots of the
group holding the record's node (1136 bytes). -/
def capRecord (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    List Byte :=
  saltBytes salt ++
  (List.range 7).flatMap fun k =>
    (List.range 5).flatMap fun t => digestBytes (pentaNode penta leaves k (5 * (index.val / 5 ^ (k + 1)) + t))

/-- Every slot of level `k`, in group order. -/
def capLevel (penta : PentaFunction) (leaves : DigestTape) (k : Nat) : List Byte :=
  (List.range (capSlots k)).flatMap fun j => digestBytes (pentaNode penta leaves k j)

/-- The table of levels 7 to 10 (8,800 bytes). -/
def capTable (penta : PentaFunction) (leaves : DigestTape) : List Byte :=
  [7, 8, 9, 10].flatMap (capLevel penta leaves)

/-- Records in ascending position order, then the first 8,704 bytes of the table.
An empty opening has no table. -/
def capTranscriptBuilderOld : PentaTranscriptBuilder :=
  fun penta positions salts leaves =>
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    (pentaRoot penta leaves,
      ordered.flatMap (fun index => capRecord penta leaves index.val (salts index)) ++
        (if positions.card = 0 then [] else (capTable penta leaves).take 8704))

theorem cap_record_length (penta : PentaFunction) (leaves : DigestTape) (index : Index)
    (salt : BitVec 128) : (capRecord penta leaves index salt).length = 1136 := by
  have inner : ∀ k, ((List.range 5).flatMap fun t =>
      digestBytes (pentaNode penta leaves k (5 * (index.val / 5 ^ (k + 1)) + t))).length = 160 := by
    intro k
    simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]
  unfold capRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, inner, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul]

theorem cap_level_length (penta : PentaFunction) (leaves : DigestTape) (k : Nat) :
    (capLevel penta leaves k).length = 32 * capSlots k := by
  unfold capLevel
  simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul]
  ring

theorem cap_table_length (penta : PentaFunction) (leaves : DigestTape) :
    (capTable penta leaves).length = 8800 := by
  obtain ⟨a, b, c, d⟩ := cap_slots_values
  simp [capTable, cap_level_length, a, b, c, d]

/-- Proof bytes of the cap format. -/
def capLengthOld (positions : Positions) : Nat :=
  1136 * positions.card + (if positions.card = 0 then 0 else 8704)

theorem cap_proof_length_old (penta : PentaFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    (capTranscriptBuilderOld penta positions salts leaves).2.length = capLengthOld positions := by
  simp only [capTranscriptBuilderOld, List.length_append, List.length_flatMap, cap_record_length,
    List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_sort, Finset.card_attach, capLengthOld]
  split <;> simp [cap_table_length, Nat.mul_comm]

/-- The submitted format: records in ascending position order, then every slot of level 7
(6,880 bytes); the checker recomputes levels 8 to 10. An empty opening has no table. -/
def capTranscriptBuilder : PentaTranscriptBuilder :=
  fun penta positions salts leaves =>
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    (pentaRoot penta leaves,
      ordered.flatMap (fun index => capRecord penta leaves index.val (salts index)) ++
        (if positions.card = 0 then [] else capLevel penta leaves 7))

def capLength (positions : Positions) : Nat :=
  1136 * positions.card + (if positions.card = 0 then 0 else 6880)

theorem cap_proof_length (penta : PentaFunction) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) :
    (capTranscriptBuilder penta positions salts leaves).2.length = capLength positions := by
  simp only [capTranscriptBuilder, List.length_append, List.length_flatMap, cap_record_length,
    List.map_const', List.sum_replicate, smul_eq_mul, Finset.length_sort, Finset.card_attach, capLength]
  split <;> simp [cap_level_length, cap_slots_values, Nat.mul_comm]

theorem cap_transcript_builder_local : PentaBuildLocal capTranscriptBuilder := by
  intro penta penta' positions salts leaves same
  have nodes := penta_node_congr penta penta' leaves same
  have root : pentaRoot penta leaves = pentaRoot penta' leaves := nodes _ le_rfl _
  have record : ∀ index salt, capRecord penta leaves index salt = capRecord penta' leaves index salt := by
    intro index salt
    unfold capRecord
    congr 1
    apply List.flatMap_congr
    intro k member
    apply List.flatMap_congr
    intro t _
    have small : k ≤ PENTA_LEVELS := by
      have := List.mem_range.mp member
      unfold PENTA_LEVELS
      omega
    rw [nodes k small]
  have table : capLevel penta leaves 7 = capLevel penta' leaves 7 := by
    unfold capLevel
    apply List.flatMap_congr
    intro j _
    rw [nodes 7 (by unfold PENTA_LEVELS; omega)]
  simp only [capTranscriptBuilder, root, record, table]

end TwoPermutationPrototype.Sampling
