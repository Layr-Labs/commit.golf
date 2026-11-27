import CommitGolfCandidate.QuadOpeningABI
import CommitGolfCandidate.QuadOpeningModel

/-! The decoded opening output is `proofFromTrapdoor`: the 688-byte records, then the table. -/

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

/-- A 32-byte slot copied from the trapdoor: four output doublewords starting at `u`. -/
theorem slot_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (u k g t : Nat) (hk : k < 22) (hg : g < pentaCount (k+1))
    (ht : t < 5)
    (out : ∀ w < 4, state.getMem (BitVec.ofNat 64 (proofBase+8*(u+w))) =
      (s.initialState .opening (trapdoor, positions)).getMem
        (BitVec.ofNat 64 (trapdoorBase+pentaGroupSlotOffset k g t+8*w))) :
    bytesAt state (proofBase+8*u) 32 = digestBytes (pentaTrapdoorSlot trapdoor k g t) := by
  have room := group_room k hk
  have al := group_aligned k (by omega)
  have tb : trapdoorBase = 4294971424 := rfl
  have pb : proofBase = 10804535392 := rfl
  have gb : 368*g+368 ≤ 368*pentaCount (k+1) := by have := Nat.mul_le_mul_left 368 hg; omega
  have copied := QOpening.copied_buffer (s.initialState .opening (trapdoor, positions)) state
    (trapdoorBase+pentaGroupSlotOffset k g t) (proofBase+8*u) 4
    (by unfold pentaGroupSlotOffset; omega) (by omega) (by decide) (fun w hw => by
      rw [show proofBase+8*u+8*w = proofBase+8*(u+w) by omega]; exact out w hw)
  have slice := QOpening.input_trapdoor_slice s layout trapdoor positions
    (pentaGroupSlotOffset k g t) 32 (by unfold pentaGroupSlotOffset QOpening.trapdoorBytes; omega)
  exact bytes_at_serialized state _ 32 _ (copied.trans slice)

theorem record_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (o : Nat) (present : o < positions.card)
    (out : Inv (s.initialState .opening (trapdoor, positions)) state (proofSource positions) (proofWords positions)) :
    bytesAt state (proofBase+688*o) 688 =
      trapdoorRecord (s := s) trapdoor ((positions.sort (· ≤ ·))[o]'(by simpa using present)) := by
  let init := s.initialState .opening (trapdoor, positions)
  let index := (positions.sort (· ≤ ·))[o]'(by simpa using present)
  have named : ordinalIndex positions o = index.val := ordinal_index positions o present
  have inside := index.isLt
  have hL : LENGTH = 16777216 := rfl
  have words : proofWords positions = 86*positions.card+656 := by simp [proofWords, Nat.pos_iff_ne_zero.mp
    (Nat.lt_of_le_of_lt (Nat.zero_le o) present)]
  have word (d : Nat) (live : d < 86) : state.getMem (BitVec.ofNat 64 (proofBase+8*(86*o+d))) =
      init.getMem (BitVec.ofNat 64 (wordSource positions (86*o+d))) := by
    have h := out.output (86*o+d) (by rw [words]; omega)
    unfold proofSource at h
    rw [if_pos (by omega)] at h
    exact h
  -- salt
  have saltRead : readBuffer state (proofBase+688*o) 16 = trapdoorSalt (s := s) trapdoor index := by
    have copied := QOpening.copied_buffer init state (nonceBase+16*index.val) (proofBase+688*o) 2
      (by have : nonceBase % 8 = 0 := by decide
          omega) (by have : proofBase % 8 = 0 := by decide
                     omega) (by decide) (fun w hw => by
        rw [show proofBase+688*o+8*w = proofBase+8*(86*o+w) by omega, word w (by omega),
          word_source_salt positions o w hw, named])
    exact copied.trans (QOpening.input_nonce s layout trapdoor positions index)
  have part₁ : bytesAt state (proofBase+688*o) 16 = saltBytes (trapdoorSalt (s := s) trapdoor index) :=
    bytes_at_serialized state _ 16 _ saltRead
  -- the 5-ary levels
  have pslot (k j : Nat) (hk : k < 2) (hj : j < 4) :
      bytesAt state (proofBase+688*o+16+128*k+32*j) 32 =
        digestBytes (pentaTrapdoorSlot trapdoor k (index.val / placeValue (k + 1)) (pentaRot index k j).val) := by
    rw [show proofBase+688*o+16+128*k+32*j = proofBase+8*(86*o+2+16*k+4*j) by omega]
    have count := div_lt_count index.val inside (k+1)
    have rot : (pentaRot index k j).val = (index.val/5^k%5+j+1)%5 := by
      show (hybridSlot index.val k + j + 1) % 5 = _
      unfold hybridSlot
      rw [place_value_low k (by omega)]
      rw [slot_base_low k (by unfold PENTA_LOW; omega), radix_low k (by unfold PENTA_LOW; omega)]
      simp
    rw [rot, place_value_low (k+1) (by omega)]
    rw [place_value_low (k+1) (by omega)] at count
    apply slot_bytes s layout trapdoor positions state _ k _ _ (by omega) count (Nat.mod_lt _ (by decide))
    intro w hw
    rw [show 86*o+2+16*k+4*j+w = 86*o+(2+16*k+4*j+w) by omega, word _ (by omega),
      show 86*o+(2+16*k+4*j+w) = 86*o+2+16*k+4*j+w by omega, word_source_penta positions o k j w hk hj hw, named]
  have part₂ : bytesAt state (proofBase+688*o+16) (128*(List.range PENTA_LOW).length) =
      (List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaTrapdoorSlot trapdoor k (index.val / placeValue (k + 1)) (pentaRot index k j).val) := by
    apply bytes_at_chunks
    intro k hk
    have bound : k < 2 := by simpa [PENTA_LOW] using hk
    rw [List.getElem_range]
    have inner := bytes_at_chunks state (proofBase+688*o+16+128*k) 32 (List.range 4)
      (fun j => digestBytes (pentaTrapdoorSlot trapdoor k (index.val / placeValue (k + 1)) (pentaRot index k j).val))
      (fun j hj => by
        rw [List.getElem_range]
        exact pslot k j bound (by simpa using hj))
    simpa using inner
  -- the 4-ary level
  have qslot (j : Nat) (hj : j < 3) :
      bytesAt state (proofBase+688*o+272+32*j) 32 =
        digestBytes (pentaTrapdoorSlot trapdoor QUAD_LEVEL (index.val / placeValue (QUAD_LEVEL + 1)) (quadSib index QUAD_LEVEL j).val) := by
    rw [show proofBase+688*o+272+32*j = proofBase+8*(86*o+34+4*j) by omega]
    have count := div_lt_count index.val inside 3
    have sib : (quadSib index QUAD_LEVEL j).val = 1+(index.val/25%4+j+1)%4 := rfl
    have grp : index.val / placeValue (QUAD_LEVEL + 1) = index.val/25/4 := by
      rw [show placeValue (QUAD_LEVEL + 1) = 100 from rfl, Nat.div_div_eq_div_mul]
    rw [sib, grp, show QUAD_LEVEL = 2 from rfl]
    rw [show placeValue 3 = 100 from rfl] at count
    replace count : index.val/25/4 < pentaCount (2+1) := by rw [Nat.div_div_eq_div_mul]; exact count
    apply slot_bytes s layout trapdoor positions state _ 2 _ _ (by omega) count (by omega)
    intro w hw
    rw [show 86*o+34+4*j+w = 86*o+(34+4*j+w) by omega, word _ (by omega),
      show 86*o+(34+4*j+w) = 86*o+34+4*j+w by omega, word_source_quad positions o j w hj hw, named]
  have partQ : bytesAt state (proofBase+688*o+272) (32*(List.range 3).length) =
      (List.range 3).flatMap fun j =>
        digestBytes (pentaTrapdoorSlot trapdoor QUAD_LEVEL (index.val / placeValue (QUAD_LEVEL + 1)) (quadSib index QUAD_LEVEL j).val) := by
    apply bytes_at_chunks
    intro j hj
    rw [List.getElem_range]
    exact qslot j (by simpa using hj)
  -- the binary levels
  have bslot (m : Nat) (hm : m < 10) :
      bytesAt state (proofBase+688*o+368+32*m) 32 =
        digestBytes (pentaTrapdoorSlot trapdoor (BIN_LOW+m) (index.val / placeValue (BIN_LOW+m+1))
          (binSibling index (BIN_LOW+m)).val) := by
    rw [show proofBase+688*o+368+32*m = proofBase+8*(86*o+46+4*m) by omega]
    have count := div_lt_count index.val inside (3+(m+1))
    have sib : (binSibling index (BIN_LOW+m)).val = 4-index.val/(100*2^m)%2 := by
      show 3 + (1 - index.val / placeValue (BIN_LOW+m) % 2) = _
      rw [show BIN_LOW+m = 3+m from rfl, place_value_bin m (by omega)]; omega
    have grp : index.val / placeValue (BIN_LOW+m+1) = index.val/(100*2^m)/2 := by
      rw [show BIN_LOW+m+1 = 3+(m+1) from rfl, place_value_bin (m+1) (by omega), Nat.div_div_eq_div_mul, pow_succ]
      ring_nf
    rw [sib, grp, show BIN_LOW+m = 3+m from rfl]
    rw [place_value_bin (m+1) (by omega)] at count
    have e : index.val/(100*2^m)/2 = index.val/(100*2^(m+1)) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_assoc]
    replace count : index.val/(100*2^m)/2 < pentaCount (3+m+1) := by rw [e]; simpa [Nat.add_assoc] using count
    apply slot_bytes s layout trapdoor positions state _ (3+m) _ _ (by omega) count (by omega)
    intro w hw
    rw [show 86*o+46+4*m+w = 86*o+(46+4*m+w) by omega, word _ (by omega),
      show 86*o+(46+4*m+w) = 86*o+46+4*m+w by omega, word_source_bin positions o m w hm hw, named]
  have part₃ : bytesAt state (proofBase+688*o+368) (32*(List.range (CAP_LEVEL-BIN_LOW)).length) =
      (List.range (CAP_LEVEL-BIN_LOW)).flatMap fun m =>
        digestBytes (pentaTrapdoorSlot trapdoor (BIN_LOW+m) (index.val / placeValue (BIN_LOW+m+1))
          (binSibling index (BIN_LOW+m)).val) := by
    apply bytes_at_chunks
    intro m hm
    rw [List.getElem_range]
    exact bslot m (by simpa [CAP_LEVEL, BIN_LOW] using hm)
  have split : bytesAt state (proofBase+688*o) 688 =
      bytesAt state (proofBase+688*o) 16 ++
        bytesAt state (proofBase+688*o+16) (128*(List.range PENTA_LOW).length) ++
        bytesAt state (proofBase+688*o+272) (32*(List.range 3).length) ++
        bytesAt state (proofBase+688*o+368) (32*(List.range (CAP_LEVEL-BIN_LOW)).length) := by
    rw [show (688 : Nat) = ((16+128*(List.range PENTA_LOW).length)+32*(List.range 3).length)+32*(List.range (CAP_LEVEL-BIN_LOW)).length by
        simp [PENTA_LOW, CAP_LEVEL, BIN_LOW], bytes_at_append, bytes_at_append, bytes_at_append]
    simp [PENTA_LOW]
  rw [split, part₁, part₂, partQ, part₃]
  rfl

theorem table_bytes (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (nonempty : positions.card ≠ 0)
    (out : Inv (s.initialState .opening (trapdoor, positions)) state (proofSource positions) (proofWords positions)) :
    bytesAt state (proofBase+688*positions.card) 5248 = trapdoorTable trapdoor := by
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have words : proofWords positions = 86*positions.card+656 := by simp [proofWords, nonempty]
  have c14 : pentaCount CAP_LEVEL = 164 := cap_count_value
  have node (j : Nat) (hj : j < 164) :
      bytesAt state (proofBase+688*positions.card+32*j) 32 =
        digestBytes (pentaTrapdoorSlot trapdoor CAP_LEVEL (j/5) (j%5)) := by
    rw [show proofBase+688*positions.card+32*j = proofBase+8*(86*positions.card+4*j) by omega]
    apply slot_bytes s layout trapdoor positions state _ CAP_LEVEL _ _ (by decide)
      (by change j/5 < pentaCount 14; have : pentaCount 14 = 33 := by decide
          omega) (by omega)
    intro w hw
    have h := out.output (86*positions.card+4*j+w) (by rw [words]; omega)
    unfold proofSource at h
    rw [if_neg (by omega), show 86*positions.card+4*j+w-86*positions.card = 4*j+w by omega,
      table_source_eq] at h
    rw [show 86*positions.card+4*j+w = 86*positions.card+4*j+w from rfl, h]
    congr 2
    unfold hybTableStart pentaGroupSlotOffset CAP_LEVEL
    omega
  have level : bytesAt state (proofBase+688*positions.card) (32*(List.range 164).length) =
      (List.range 164).flatMap fun j => digestBytes (pentaTrapdoorSlot trapdoor CAP_LEVEL (j/5) (j%5)) := by
    apply bytes_at_chunks
    intro j hj
    rw [List.getElem_range]
    exact node j (by simpa using hj)
  simp only [List.length_range] at level
  unfold trapdoorTable
  rw [c14]
  exact level

theorem read_opening_proof (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (result : Execution)
    (physical : OpenPhysical s trapdoor positions result) :
    s.readProof result = proofFromTrapdoor (s := s) trapdoor positions := by
  have success := opening_success s abi trapdoor positions result physical
  simp only [Submission.readProof, success, ite_true, physical.length, abi.toOpeningLayout.proof]
  change bytesAt result.state proofBase (proofLength positions) = _
  have length : (positions.sort (· ≤ ·)).length = positions.card := Finset.length_sort _
  have records : bytesAt result.state proofBase (688*positions.card) =
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
