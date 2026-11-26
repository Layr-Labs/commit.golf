import CommitGolfCandidate.QuadOpeningABI
import CommitGolfCandidate.QuadOpeningModel

/-! The decoded opening output is `proofFromTrapdoor`: the 1136-byte records, then the table. -/

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
    bytesAt state (proofBase+1136*o) 1136 =
      trapdoorRecord (s := s) trapdoor ((positions.sort (· ≤ ·))[o]'(by simpa using present)) := by
  let init := s.initialState .opening (trapdoor, positions)
  let index := (positions.sort (· ≤ ·))[o]'(by simpa using present)
  have named : ordinalIndex positions o = index.val := ordinal_index positions o present
  have inside := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have proofAligned : proofBase % 8 = 0 := by decide
  have words : proofWords positions = 142*positions.card+860 := by simp [proofWords, Nat.pos_iff_ne_zero.mp
    (Nat.lt_of_le_of_lt (Nat.zero_le o) present)]
  have word (d : Nat) (live : d < 142) : state.getMem (BitVec.ofNat 64 (proofBase+1136*o+8*d)) =
      init.getMem (BitVec.ofNat 64 (wordSource positions (142*o+d))) := by
    rw [show proofBase+1136*o+8*d = proofBase+8*(142*o+d) by omega]
    have h := out.output (142*o+d) (by rw [words]; omega)
    unfold proofSource at h
    rw [if_pos (by omega)] at h
    exact h
  -- salt
  have saltRead : readBuffer state (proofBase+1136*o) 16 = trapdoorSalt (s := s) trapdoor index := by
    have copied := QOpening.copied_buffer init state (nonceBase+16*index.val) (proofBase+1136*o) 2
      (by have : nonceBase % 8 = 0 := by decide
          omega) (by omega) (by decide) (fun w hw => by
        rw [word w (by omega), word_source_salt positions o w hw, named])
    exact copied.trans (QOpening.input_nonce s layout trapdoor positions index)
  have part₁ : bytesAt state (proofBase+1136*o) 16 = saltBytes (trapdoorSalt (s := s) trapdoor index) :=
    bytes_at_serialized state _ 16 _ saltRead
  -- the five slots of each level-0..6 group
  have child (k t : Nat) (hk : k < 7) (ht : t < 5) :
      bytesAt state (proofBase+1136*o+16+160*k+32*t) 32 =
        digestBytes (pentaTrapdoorNode trapdoor k (5 * (index.val / 5 ^ (k + 1)) + t)) := by
    have room := group_room k (by omega)
    have count := div_lt_count index.val inside (k+1)
    have al := group_aligned k (by omega)
    have tb : trapdoorBase = 4294971424 := rfl
    have pb : proofBase = 10804535392 := rfl
    have offset : pentaSlotOffset k (5 * (index.val / 5 ^ (k + 1)) + t) =
        pentaGroupBase k + 40 + 368*(index.val / 5 ^ (k + 1)) + 32*t := by
      unfold pentaSlotOffset
      rw [show (5 * (index.val / 5 ^ (k + 1)) + t) / 5 = index.val / 5 ^ (k + 1) by omega,
        show (5 * (index.val / 5 ^ (k + 1)) + t) % 5 = t by omega]
      omega
    have gb : 368*(index.val / 5 ^ (k + 1)) + 368 ≤ 368*pentaCount (k+1) := by
      have := Nat.mul_le_mul_left 368 (show index.val / 5 ^ (k + 1) + 1 ≤ pentaCount (k+1) by omega)
      omega
    have copied := QOpening.copied_buffer init state
      (trapdoorBase+pentaSlotOffset k (5 * (index.val / 5 ^ (k + 1)) + t)) (proofBase+1136*o+16+160*k+32*t) 4
      (by rw [offset]; omega) (by omega) (by decide) (fun w hw => by
        rw [show proofBase+1136*o+16+160*k+32*t+8*w = proofBase+1136*o+8*(2+20*k+(4*t+w)) by omega,
          word _ (by omega), show 142*o+(2+20*k+(4*t+w)) = 142*o+2+20*k+(4*t+w) by omega,
          word_source_level positions o k (4*t+w) hk (by omega), named, offset]
        congr 2
        omega)
    have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
      (pentaSlotOffset k (5 * (index.val / 5 ^ (k + 1)) + t)) 32 (by
        rw [offset]
        unfold QOpening.trapdoorBytes
        omega)
    have value : readBuffer state (proofBase+1136*o+16+160*k+32*t) 32 =
        pentaTrapdoorNode trapdoor k (5 * (index.val / 5 ^ (k + 1)) + t) := copied.trans slice
    exact bytes_at_serialized state _ 32 _ value
  have part₂ : bytesAt state (proofBase+1136*o+16) (160*(List.range 7).length) =
      (List.range 7).flatMap fun k =>
        (List.range 5).flatMap fun t => digestBytes (pentaTrapdoorNode trapdoor k (5 * (index.val / 5 ^ (k + 1)) + t)) := by
    apply bytes_at_chunks
    intro k hk
    have bound : k < 7 := by simpa using hk
    rw [List.getElem_range]
    have inner := bytes_at_chunks state (proofBase+1136*o+16+160*k) 32 (List.range 5)
      (fun t => digestBytes (pentaTrapdoorNode trapdoor k (5 * (index.val / 5 ^ (k + 1)) + t)))
      (fun t ht => by
        rw [List.getElem_range]
        exact child k t bound (by simpa using ht))
    simpa using inner
  have split : bytesAt state (proofBase+1136*o) 1136 =
      bytesAt state (proofBase+1136*o) 16 ++
        bytesAt state (proofBase+1136*o+16) (160*(List.range 7).length) := by
    rw [show (1136 : Nat) = 16+160*(List.range 7).length by simp, bytes_at_append]
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
    bytesAt state (proofBase+1136*positions.card) 6880 = trapdoorLevel trapdoor 7 := by
  let init := s.initialState .opening (trapdoor, positions)
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have proofAligned : proofBase % 8 = 0 := by decide
  have words : proofWords positions = 142*positions.card+860 := by simp [proofWords, nonempty]
  have s7 : capSlots 7 = 215 := cap_slots_values.1
  -- Slot `j` of level 7.
  have slot (j : Nat) (hj : j < 215) :
      bytesAt state (proofBase+1136*positions.card+32*j) 32 = digestBytes (pentaTrapdoorNode trapdoor 7 j) := by
    have full : j < capSlots (7+0) := by rw [show 7+0 = 7 from rfl, s7]; exact hj
    have room := group_room 7 (by omega)
    have c8 : pentaCount (7+1) = 43 := by decide
    rw [c8] at room
    have offsetBound : pentaSlotOffset 7 j + 32 ≤ 1543577600 := by
      unfold capSlots at full
      unfold pentaSlotOffset
      omega
    have tb : trapdoorBase % 8 = 0 := by decide
    have aligned : (trapdoorBase + pentaSlotOffset 7 j) % 8 = 0 := by
      have := group_aligned' 0 (by decide)
      simp only [Nat.add_zero] at this
      unfold pentaSlotOffset
      omega
    have copied := QOpening.copied_buffer init state (trapdoorBase + pentaSlotOffset 7 j)
      (proofBase+1136*positions.card+32*j) 4 aligned (by omega) (by decide) (fun w hw => by
        rw [show proofBase+1136*positions.card+32*j+8*w =
          proofBase+8*(142*positions.card+(20*tableFirst 0+(4*j+w))) by simp [tableFirst]; omega]
        have h := out.output (142*positions.card+(20*tableFirst 0+(4*j+w))) (by rw [words]; simp [tableFirst]; omega)
        unfold proofSource at h
        rw [if_neg (by omega), Nat.add_sub_cancel_left, table_source_slot 0 j w (by decide) full hw] at h
        exact h)
    have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
      (pentaSlotOffset 7 j) 32 (by unfold QOpening.trapdoorBytes; omega)
    exact bytes_at_serialized state _ 32 _ (copied.trans slice)
  have level : bytesAt state (proofBase+1136*positions.card) (32*(List.range 215).length) =
      (List.range 215).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor 7 j) := by
    apply bytes_at_chunks
    intro j hj
    rw [List.getElem_range]
    exact slot j (by simpa using hj)
  simp only [List.length_range] at level
  unfold trapdoorLevel
  rw [s7]
  exact level

theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have success := opening_success s abi trapdoor positions result physical
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  have records : bytesAt result.state proofBase (1136*positions.card) =
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
