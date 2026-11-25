import CommitGolfCandidate.QuadOpeningABI
import CommitGolfCandidate.QuadOpeningModel

/-! The decoded opening output is `proofFromTrapdoor`: the 912-byte records, then the table. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open QOpening (OpeningLayout trapdoorSalt proofBase nonceBase trapdoorBase)

private def bytesAt (state : MachineState) (address count : Nat) : List Byte :=
  (List.range count).map fun j => state.getByte (BitVec.ofNat 64 (address+j))

private theorem bytes_at_append (state : MachineState) (address left right : Nat) :
    bytesAt state address (left+right) =
      bytesAt state address left ++ bytesAt state (address+left) right := by
  simp [bytesAt, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem bytes_at_serialized (state : MachineState) (address count : Nat)
    (value : BitVec (8*count)) (serialization : readBuffer state address count = value) :
    bytesAt state address count = List.ofFn (fun i : Fin count => value.extractLsb' (8*i.val) 8) := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i left right
    have inside : i < count := by simpa [bytesAt] using left
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [← serialization, read_buffer_byte state address count i inside]

private theorem bytes_at_chunks {α : Type} (state : MachineState) (address width : Nat) (items : List α)
    (itemBytes : α → List Byte)
    (reads : ∀ j (inside : j < items.length),
      bytesAt state (address+width*j) width = itemBytes items[j]) :
    bytesAt state address (width*items.length) = items.flatMap itemBytes := by
  induction items generalizing address with
  | nil => simp [bytesAt]
  | cons first rest ih =>
    have head := reads 0 (by simp)
    have tail : ∀ j (inside : j < rest.length),
        bytesAt state (address + width + width*j) width = itemBytes rest[j] := by
      intro j inside
      have same := reads (j+1) (by simpa)
      simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using same
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm (width*rest.length) width, bytes_at_append,
      List.flatMap_cons, ih (address+width) tail]
    simpa using head

theorem record_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (o : Nat) (present : o < positions.card)
    (out : Inv (s.initialState .opening (trapdoor, positions)) state (proofSource positions) (proofWords positions)) :
    bytesAt state (proofBase+912*o) 912 =
      trapdoorRecord (s := s) trapdoor ((positions.sort (· ≤ ·))[o]'(by simpa using present)) := by
  let init := s.initialState .opening (trapdoor, positions)
  let index := (positions.sort (· ≤ ·))[o]'(by simpa using present)
  have named : ordinalIndex positions o = index.val := ordinal_index positions o present
  have inside := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have proofAligned : proofBase % 8 = 0 := by decide
  have words : proofWords positions = 114*positions.card+1100 := by simp [proofWords, Nat.pos_iff_ne_zero.mp
    (Nat.lt_of_le_of_lt (Nat.zero_le o) present)]
  have word (d : Nat) (live : d < 114) : state.getMem (BitVec.ofNat 64 (proofBase+912*o+8*d)) =
      init.getMem (BitVec.ofNat 64 (wordSource positions (114*o+d))) := by
    rw [show proofBase+912*o+8*d = proofBase+8*(114*o+d) by omega]
    have h := out.output (114*o+d) (by rw [words]; omega)
    unfold proofSource at h
    rw [if_pos (by omega)] at h
    exact h
  -- salt
  have saltRead : readBuffer state (proofBase+912*o) 16 = trapdoorSalt (s := s) trapdoor index := by
    have copied := QOpening.copied_buffer init state (nonceBase+16*index.val) (proofBase+912*o) 2
      (by have : nonceBase % 8 = 0 := by decide
          omega) (by omega) (by decide) (fun w hw => by
        rw [word w (by omega), word_source_salt positions o w hw, named])
    exact copied.trans (QOpening.input_nonce s layout trapdoor positions index)
  have part₁ : bytesAt state (proofBase+912*o) 16 = saltBytes (trapdoorSalt (s := s) trapdoor index) :=
    bytes_at_serialized state _ 16 _ saltRead
  -- children of levels 0-6
  have child (k j : Nat) (hk : k < 7) (hj : j < 4) :
      bytesAt state (proofBase+912*o+16+128*k+32*j) 32 =
        digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)) := by
    have source := neighbour_source index.val k j inside (by omega) hj
    have copied := QOpening.copied_buffer init state
      (trapdoorBase+pentaSlotOffset k (neighbourNat index.val k j)) (proofBase+912*o+16+128*k+32*j) 4
      source.2.1 (by omega) (by decide) (fun w hw => by
        rw [show proofBase+912*o+16+128*k+32*j+8*w = proofBase+912*o+8*(2+16*k+4*j+w) by omega,
          word _ (by omega), show 114*o+(2+16*k+4*j+w) = 114*o+2+16*k+4*j+w by omega,
          word_source_level positions o k j w hk hj hw, named])
    have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
      (pentaSlotOffset k (neighbourNat index.val k j)) 32 (by
        have := source.2.2.2
        unfold QOpening.trapdoorBytes
        omega)
    have value : readBuffer state (proofBase+912*o+16+128*k+32*j) 32 =
        pentaTrapdoorNode trapdoor k (pentaNeighbour index k j) := copied.trans slice
    exact bytes_at_serialized state _ 32 _ value
  have part₂ : bytesAt state (proofBase+912*o+16) (128*(List.range 7).length) =
      (List.range 7).flatMap fun k =>
        (List.range 4).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)) := by
    apply bytes_at_chunks
    intro k hk
    have bound : k < 7 := by simpa using hk
    rw [List.getElem_range]
    have inner := bytes_at_chunks state (proofBase+912*o+16+128*k) 32 (List.range 4)
      (fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j)))
      (fun j hj => by
        rw [List.getElem_range]
        exact child k j bound (by simpa using hj))
    simpa using inner
  have split : bytesAt state (proofBase+912*o) 912 =
      bytesAt state (proofBase+912*o) 16 ++
        bytesAt state (proofBase+912*o+16) (128*(List.range 7).length) := by
    rw [show (912 : Nat) = 16+128*(List.range 7).length by simp, bytes_at_append]
  rw [split, part₁, part₂]
  rfl

/-- Table doubleword `20 · tableFirst L + 4 j + w` is doubleword `w` of slot `j` of level `7 + L`. -/
theorem table_source_slot (L j w : Nat) (hL : L < 4) (hj : j < capSlots (7+L)) (hw : w < 4) :
    tableSource (20*tableFirst L + (4*j+w)) = trapdoorBase + pentaSlotOffset (7+L) j + 8*w := by
  have group : j/5 < pentaCount (7+L+1) := by unfold capSlots at hj; omega
  have h := table_source_group L (j/5) (4*(j%5)+w) hL group (by omega)
  rw [show 20*(tableFirst L + j/5) + (4*(j%5)+w) = 20*tableFirst L + (4*j+w) by omega] at h
  rw [h]
  unfold pentaSlotOffset
  omega

theorem table_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (nonempty : positions.card ≠ 0)
    (out : Inv (s.initialState .opening (trapdoor, positions)) state (proofSource positions) (proofWords positions)) :
    bytesAt state (proofBase+912*positions.card) 8800 = trapdoorTable trapdoor := by
  let init := s.initialState .opening (trapdoor, positions)
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have proofAligned : proofBase % 8 = 0 := by decide
  have words : proofWords positions = 114*positions.card+1100 := by simp [proofWords, nonempty]
  have slots := cap_slots_values
  -- slot `j` of table level `L`
  have slot (L j : Nat) (hL : L < 4) (hj : j < capSlots (7+L)) :
      bytesAt state (proofBase+912*positions.card+160*tableFirst L+32*j) 32 =
        digestBytes (pentaTrapdoorNode trapdoor (7+L) j) := by
    have first : 20*tableFirst L + 4*capSlots (7+L) ≤ 1100 := by
      obtain ⟨s7, s8, s9, s10⟩ := slots
      interval_cases L <;> simp only [tableFirst, Nat.reduceAdd, s7, s8, s9, s10] at hj ⊢ <;> omega
    have room := group_room (7+L) (by omega)
    have offsetBound : pentaSlotOffset (7+L) j + 32 ≤ 1543577600 := by
      unfold capSlots at hj
      unfold pentaSlotOffset
      omega
    have tb : trapdoorBase % 8 = 0 := by decide
    have aligned : (trapdoorBase + pentaSlotOffset (7+L) j) % 8 = 0 := by
      have := group_aligned' L hL
      unfold pentaSlotOffset
      omega
    have copied := QOpening.copied_buffer init state (trapdoorBase + pentaSlotOffset (7+L) j)
      (proofBase+912*positions.card+160*tableFirst L+32*j) 4 aligned (by omega) (by decide) (fun w hw => by
        rw [show proofBase+912*positions.card+160*tableFirst L+32*j+8*w =
          proofBase+8*(114*positions.card+(20*tableFirst L+(4*j+w))) by omega]
        have h := out.output (114*positions.card+(20*tableFirst L+(4*j+w))) (by rw [words]; omega)
        unfold proofSource at h
        rw [if_neg (by omega), Nat.add_sub_cancel_left, table_source_slot L j w hL hj hw] at h
        exact h)
    have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
      (pentaSlotOffset (7+L) j) 32 (by unfold QOpening.trapdoorBytes; omega)
    exact bytes_at_serialized state _ 32 _ (copied.trans slice)
  -- one table level
  have level (L : Nat) (hL : L < 4) :
      bytesAt state (proofBase+912*positions.card+160*tableFirst L) (32*(List.range (capSlots (7+L))).length) =
        (List.range (capSlots (7+L))).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor (7+L) j) := by
    apply bytes_at_chunks
    intro j hj
    rw [List.getElem_range]
    exact slot L j hL (by simpa using hj)
  obtain ⟨s7, s8, s9, s10⟩ := slots
  have l0 := level 0 (by decide)
  have l1 := level 1 (by decide)
  have l2 := level 2 (by decide)
  have l3 := level 3 (by decide)
  simp only [List.length_range, Nat.reduceAdd, s7, s8, s9, s10, tableFirst] at l0 l1 l2 l3
  unfold trapdoorTable
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, s7, s8, s9, s10]
  rw [show (8800 : Nat) = 32*215 + (32*45 + (32*10 + 32*5)) by rfl, bytes_at_append, bytes_at_append,
    bytes_at_append]
  rw [show proofBase+912*positions.card+32*215 = proofBase+912*positions.card+160*43 by rfl,
    show proofBase+912*positions.card+160*43+32*45 = proofBase+912*positions.card+160*52 by omega,
    show proofBase+912*positions.card+160*52+32*10 = proofBase+912*positions.card+160*54 by omega]
  rw [show proofBase+912*positions.card = proofBase+912*positions.card+160*0 by rfl, l0]
  simp only [Nat.mul_zero, Nat.add_zero] at l0 ⊢
  rw [l1, l2, l3]

theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have success := opening_success s abi trapdoor positions result physical
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  have records : bytesAt result.state proofBase (912*positions.card) =
      (positions.sort (· ≤ ·)).flatMap (trapdoorRecord (s := s) trapdoor) := by
    rw [← length]
    apply bytes_at_chunks
    intro o inside
    exact record_bytes s abi.toOpeningLayout trapdoor positions result.state o (by simpa using inside)
      physical.output
  unfold proofFromTrapdoor proofLength capLength
  by_cases empty : positions.card = 0
  · simp only [empty, ite_true, Nat.mul_zero, Nat.add_zero] at records ⊢
    rw [records, List.append_nil]
  · simp only [empty, ite_false]
    rw [bytes_at_append, records, table_bytes s abi.toOpeningLayout trapdoor positions result.state empty
      physical.output]

theorem opening_proof_size (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, opening_success s abi trapdoor positions result physical,
    ite_true, List.length_map, List.length_range]

end TwoPermutationPrototype.QuadOpening
