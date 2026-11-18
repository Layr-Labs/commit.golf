import CommitGolfCandidate.S3LeafBytes

/-! Commitment leaf and group call: fixed-oracle memory refinement.

Leaf `l` of a block, entered with x10 = `base` (its entry minus 24): the head copies the 16-byte
nonce to `[base, base + 16)` and stores the tag `base` at `[base + 16, base + 24)`; the first call
reads `[base, base + 200)` and replies to `[base - 56, base + 144)`; the second call reads
`[base + 80, base + 280)` (first-reply bytes 136..200, then entry bytes 120..256) and replies to the
leaf's digest slot in its cell. The group call of a cell reads the cell's first 200 bytes
(72 zero bytes, four digests) and replies to the group's heap slot. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option exponentiation.threshold 4096

private theorem leaf_extract_byte (word : Word) (j : Nat) :
    extractByte word j = word.extractLsb' (8*j) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, Nat.mul_comm]

/-- The salt field of a leaf whose window starts at `base`: the nonce, then the tag `base`. -/
theorem s3_tagged_salt (r : BitVec 128) (base : Nat) (small : base < 2^64) :
    (BitVec.ofNat 256 (r.toNat + base * 2^128)).toNat % 2^192 = r.toNat + 2^128 * base := by
  have rSmall : r.toNat < 2^128 := r.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  ring

/-- The first permutation input: nonce, tag, entry bytes 0..176. -/
theorem s3_first_input (l : Nat) (state : MachineState) (base nonces cell : Nat) (r : BitVec 128)
    (value : Entry) (frame : S3LeafFrame state l base nonces cell)
    (nonce : readBuffer state (nonces + 16*l) 16 = r)
    (data : readBuffer state (base+24) 256 = value) :
    s3PermInput (s3LeafHead l state) = s3First (BitVec.ofNat 256 (r.toNat + base * 2^128)) value := by
  obtain ⟨input, source, cellPointer, unit, inputAligned, sourceAligned, cellAligned, inputLow,
    inputBound, sourceBound, cellBound, separate⟩ := frame
  have bytes (q : Nat) (hq : q < 2^64) :=
    s3_head_byte l state base nonces q input source unit inputAligned sourceAligned (by omega)
      sourceBound (by omega) hq
  have pointer : ((s3LeafHead l state).getReg .x10).toNat = base := by
    rw [s3_head_register l state .x10 (by decide) (by decide), input, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have copied : readBuffer (s3LeafHead l state) base 16 = readBuffer state (nonces + 16*l) 16 :=
    s3_read_congr _ _ _ _ 16 (fun i hi => by
      rw [bytes _ (by omega), if_pos (by omega)]
      exact s3_byte_address state _ _ (by omega))
  have tag : readBuffer (s3LeafHead l state) (base+16) 8 =
      (BitVec.ofNat 64 base).extractLsb' (8*0) (8*8) :=
    read_serialized_slice _ _ (base+16) 0 8 (fun j hj => by
      rw [bytes _ (by omega), if_neg (by omega), if_pos (by omega),
        show base + 16 + j - (base + 16) = j by omega, Nat.zero_add]
      exact leaf_extract_byte _ j)
  have tagNat : (readBuffer (s3LeafHead l state) (base+16) 8).toNat = base := by
    rw [tag, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
      Nat.mod_eq_of_lt (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have rest : readBuffer (s3LeafHead l state) (base+24) 176 = readBuffer state (base+24) 176 :=
    s3_read_congr _ _ _ _ 176 (fun i hi => by rw [bytes _ (by omega), if_neg (by omega), if_neg (by omega)])
  have whole := s3_read_append (s3LeafHead l state) base 16 184 200 (base+16) rfl rfl
  have upper := s3_read_append (s3LeafHead l state) (base+16) 8 176 184 (base+24) rfl (by omega)
  have valueNat : value.toNat = (readBuffer state (base+24) 176).toNat +
      2^1408 * (readBuffer state (base+200) 80).toNat := by
    subst data
    exact s3_read_append state (base+24) 176 80 256 (base+200) rfl (by omega)
  have small : (readBuffer state (base+24) 176).toNat < 2^1408 := (readBuffer state (base+24) 176).isLt
  unfold s3PermInput
  rw [pointer]
  apply BitVec.eq_of_toNat_eq
  unfold s3First
  refine Eq.trans ?_ (BitVec.toNat_ofNat _ _).symm
  rw [whole, upper, copied, nonce, tagNat, rest, s3_tagged_salt r base (by omega), valueNat,
    s3_split_low _ _ _ small, show 8 * 200 = 1600 from rfl,
    show (2:Nat)^(8*16) = 2^128 by norm_num, show (2:Nat)^(8*8) = 2^64 by norm_num]
  have rSmall : r.toNat < 2^128 := r.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- The second permutation input: first-reply bytes 136..200, then entry bytes 120..256. -/
theorem s3_second_input (oracle : Oracle) (l : Nat) (state : MachineState) (base nonces cell : Nat)
    (value : Entry) (frame : S3LeafFrame state l base nonces cell)
    (data : readBuffer state (base+24) 256 = value) :
    s3PermInput (s3MidState oracle l state) = s3Second (s3FirstReply oracle l state) value := by
  have bytes (q : Nat) (hq : q < 2^64) :=
    s3_mid_state_byte oracle l state base nonces cell q frame hq
  obtain ⟨input, source, cellPointer, unit, inputAligned, sourceAligned, cellAligned, inputLow,
    inputBound, sourceBound, cellBound, separate⟩ := frame
  have pointer : ((s3MidState oracle l state).getReg .x10).toNat = base+80 := by
    unfold s3MidState
    rw [s3_mid_input, s3_reply_register, s3_head_register l state .x10 (by decide) (by decide),
      s3_address _ base 80 80 input rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have chained : readBuffer (s3MidState oracle l state) (base+80) 64 =
      (s3FirstReply oracle l state).extractLsb' (8*136) (8*64) :=
    read_serialized_slice _ _ (base+80) 136 64 (fun j hj => by
      rw [bytes _ (by omega), if_pos (by omega),
        show base+80+j-(base-56) = 136+j by omega])
  have tail : readBuffer (s3MidState oracle l state) (base+144) 136 =
      readBuffer state (base+144) 136 :=
    s3_read_congr _ _ _ _ 136 (fun i hi => by rw [bytes _ (by omega), if_neg (by omega)])
  have window : (readBuffer (s3MidState oracle l state) (base+80) 200).toNat =
      (readBuffer (s3MidState oracle l state) (base+80) 64).toNat +
        2^512 * (readBuffer (s3MidState oracle l state) (base+144) 136).toNat :=
    s3_read_append _ (base+80) 64 136 200 (base+144) rfl (by omega)
  have valueNat : value.toNat = (readBuffer state (base+24) 120).toNat +
      2^960 * (readBuffer state (base+144) 136).toNat := by
    subst data
    exact s3_read_append state (base+24) 120 136 256 (base+144) rfl (by omega)
  have small : (readBuffer state (base+24) 120).toNat < 2^960 := (readBuffer state (base+24) 120).isLt
  have replySmall : (s3FirstReply oracle l state).toNat < 2^1088 * 2^512 :=
    lt_of_lt_of_eq (s3FirstReply oracle l state).isLt (by norm_num [PERMUTATION_WIDTH])
  have chainedNat : (readBuffer (s3MidState oracle l state) (base+80) 64).toNat =
      (s3FirstReply oracle l state).toNat / 2^1088 := by
    rw [chained, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul replySmall)
  have total : (readBuffer (s3MidState oracle l state) (base+80) 200).toNat < 2^(8*200) :=
    (readBuffer (s3MidState oracle l state) (base+80) 200).isLt
  unfold s3PermInput
  rw [pointer]
  apply BitVec.eq_of_toNat_eq
  unfold s3Second
  refine Eq.trans ?_ (BitVec.toNat_ofNat _ _).symm
  rw [valueNat, s3_split_high _ _ _ small, ← tail, ← chainedNat, Nat.mul_comm _ (2^512), ← window]
  exact (Nat.mod_eq_of_lt total).symm

/-- The slot pointer at the second call. -/
theorem s3_mid_slot (oracle : Oracle) (l : Nat) (state : MachineState) (base nonces cell : Nat)
    (frame : S3LeafFrame state l base nonces cell) :
    (s3MidState oracle l state).getReg .x12 = BitVec.ofNat 64 (cell + s6SlotOffset l) := by
  have notScratch : s6CellRegister (l / 4) ≠ .x6 := by unfold s6CellRegister; split_ifs <;> decide
  have notOutput : s6CellRegister (l / 4) ≠ .x12 := by unfold s6CellRegister; split_ifs <;> decide
  unfold s3MidState
  rw [s3_mid_output, s3_reply_register, s3_head_register l state _ notScratch notOutput,
    frame.cellPointer]
  exact s3_address _ cell _ _ rfl (s3_offset_extend _ (by have := s6_slot_offset l frame.unit; omega))

/-- Bytes after one leaf: the second reply at the slot, otherwise the state at the second call. -/
theorem s3_leaf_state_byte (oracle : Oracle) (l : Nat) (state : MachineState)
    (base nonces cell query : Nat) (frame : S3LeafFrame state l base nonces cell)
    (queryBound : query < 2^64) :
    (checkEvaluation oracle (s3Leaf l state)).1.getByte (BitVec.ofNat 64 query) =
      if cell + s6SlotOffset l ≤ query ∧ query < cell + s6SlotOffset l + 200 then
        (s3SecondReply oracle l state).extractLsb' (8*(query-(cell + s6SlotOffset l))) 8
      else (s3MidState oracle l state).getByte (BitVec.ofNat 64 query) := by
  rw [s3_leaf_evaluation]
  change (s3LeafTail l (s3PermReply (s3MidState oracle l state)
    (s3SecondReply oracle l state))).getByte _ = _
  rw [s3_tail_byte]
  exact s3_reply_byte (s3MidState oracle l state) (cell + s6SlotOffset l) query _
    (s3_mid_slot oracle l state base nonces cell frame) frame.cellBound queryBound

/-- The digest slot receives the leaf digest of the entry under the tagged salt. -/
theorem s3_leaf_digest (oracle : Oracle) (l : Nat) (state : MachineState)
    (base nonces cell : Nat) (r : BitVec 128) (value : Entry)
    (frame : S3LeafFrame state l base nonces cell)
    (nonce : readBuffer state (nonces + 16*l) 16 = r)
    (data : readBuffer state (base+24) 256 = value) :
    readBuffer (checkEvaluation oracle (s3Leaf l state)).1 (cell + s6SlotOffset l) 32 =
      s3LeafDigest oracle.permutation (BitVec.ofNat 256 (r.toNat + base * 2^128)) value := by
  have reply : s3SecondReply oracle l state =
      oracle.permutation (s3Second (oracle.permutation
        (s3First (BitVec.ofNat 256 (r.toNat + base * 2^128)) value)) value) := by
    unfold s3SecondReply
    rw [s3_second_input oracle l state base nonces cell value frame data]
    unfold s3FirstReply
    rw [s3_first_input l state base nonces cell r value frame nonce data]
  have cellBound := frame.cellBound
  have read := read_serialized_slice (checkEvaluation oracle (s3Leaf l state)).1
    (s3SecondReply oracle l state) (cell + s6SlotOffset l) 0 32 (fun j hj => by
      rw [s3_leaf_state_byte oracle l state base nonces cell _ frame (by omega),
        if_pos (by omega), show cell + s6SlotOffset l + j - (cell + s6SlotOffset l) = 0 + j by omega])
  rw [read, reply]
  unfold s3LeafDigest
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat]

/-- A leaf changes only `[base - 56, base + 144)` and its 200-byte reply at the slot. -/
theorem s3_leaf_preserves (oracle : Oracle) (l : Nat) (state : MachineState)
    (base nonces cell address count : Nat) (frame : S3LeafFrame state l base nonces cell)
    (bound : address+count ≤ 2^64)
    (input : address+count ≤ base - 56 ∨ base+144 ≤ address)
    (output : address+count ≤ cell + s6SlotOffset l ∨ cell + s6SlotOffset l + 200 ≤ address) :
    readBuffer (checkEvaluation oracle (s3Leaf l state)).1 address count =
      readBuffer state address count :=
  s3_read_congr _ _ _ _ count (fun i hi => by
    rw [s3_leaf_state_byte oracle l state base nonces cell _ frame (by omega),
      if_neg (by omega),
      s3_mid_state_byte oracle l state base nonces cell _ frame (by omega),
      if_neg (by omega)])

/-- Registers other than x6, x10, x12 and x21 are kept. -/
theorem s3_leaf_register (oracle : Oracle) (l : Nat) (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x6) (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12)
    (notLink : reg ≠ .x21) :
    (checkEvaluation oracle (s3Leaf l state)).1.getReg reg = state.getReg reg := by
  have other : reg ≠ s3LeafNextRegister l := by
    unfold s3LeafNextRegister
    split_ifs
    · exact notLink
    · exact notInput
  rw [s3_leaf_evaluation]
  change (s3LeafTail l (s3PermReply (s3MidState oracle l state)
    (s3SecondReply oracle l state))).getReg reg = _
  rw [s3_tail_register l _ reg other, s3_reply_register]
  unfold s3MidState
  rw [s3_mid_register l _ reg notInput notOutput, s3_reply_register,
    s3_head_register l state reg notScratch notOutput]

/-- The next window pointer: `base + 256`, in x10 (or in x21 after the block's last leaf). -/
theorem s3_leaf_link (oracle : Oracle) (l : Nat) (state : MachineState) (base : Nat)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 base) :
    (checkEvaluation oracle (s3Leaf l state)).1.getReg (s3LeafNextRegister l) = BitVec.ofNat 64 (base+256) := by
  rw [show base+256 = base+80+176 by omega, s3_leaf_evaluation]
  change (s3LeafTail l (s3PermReply (s3MidState oracle l state)
    (s3SecondReply oracle l state))).getReg (s3LeafNextRegister l) = _
  rw [s3_tail_link, s3_reply_register]
  unfold s3MidState
  rw [s3_mid_input, s3_reply_register, s3_head_register l state .x10 (by decide) (by decide),
    s3_address _ base 80 80 pointer rfl, s3_address _ (base+80) 176 176 rfl rfl]

/-! ### Group call -/

theorem s6_group_call_evaluation (oracle : Oracle) (c : Nat) (state : MachineState) :
    checkEvaluation oracle (s6GroupCall c state) =
      (s3PermReply (s6GroupCallHead c state) (oracle.permutation (s3PermInput (s6GroupCallHead c state))), 1) := by
  unfold s6GroupCall
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem s6_group_call_queries (oracle : Oracle) (c : Nat) (state : MachineState) :
    (checkEvaluation oracle (s6GroupCall c state)).2 = 1 := by
  rw [s6_group_call_evaluation]

theorem s6_group_ready_memory (c : Nat) (state : MachineState) :
    (s6GroupCallHead c state).mem = state.mem := rfl

theorem s6_group_ready_register (c : Nat) (state : MachineState) (reg : Reg)
    (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12) :
    (s6GroupCallHead c state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl notInput | exact absurd rfl notOutput | rfl

theorem s6_group_ready_input (c : Nat) (state : MachineState) (cell : Nat)
    (pointer : state.getReg (s6CellRegister c) = BitVec.ofNat 64 cell) (small : c < 16) :
    (s6GroupCallHead c state).getReg .x10 = BitVec.ofNat 64 (cell + s6CellOffset c) := by
  have value : (s6GroupCallHead c state).getReg .x10 =
      state.getReg (s6CellRegister c) + signExtend12 (BitVec.ofNat 12 (s6CellOffset c)) := rfl
  have offset := s6_cell_offset c small
  rw [value, pointer]
  exact s3_address _ cell _ _ rfl (s3_offset_extend _ (by omega))

theorem s6_group_ready_output (c : Nat) (state : MachineState) (slots : Nat)
    (pointer : state.getReg .x24 = BitVec.ofNat 64 slots) (small : c < 16) :
    (s6GroupCallHead c state).getReg .x12 = BitVec.ofNat 64 (slots + 32 * c) := by
  have value : (s6GroupCallHead c state).getReg .x12 =
      state.getReg .x24 + signExtend12 (BitVec.ofNat 12 (32 * c)) := rfl
  rw [value, pointer]
  exact s3_address _ slots _ _ rfl (s3_offset_extend _ (by omega))

/-- Bytes after a group call: the reply at its slot, otherwise unchanged. -/
theorem s6_group_call_byte (oracle : Oracle) (c : Nat) (state : MachineState) (slots query : Nat)
    (pointer : state.getReg .x24 = BitVec.ofNat 64 slots) (small : c < 16)
    (bound : slots + 32 * c + 200 ≤ 2^64) (queryBound : query < 2^64) :
    (checkEvaluation oracle (s6GroupCall c state)).1.getByte (BitVec.ofNat 64 query) =
      if slots + 32 * c ≤ query ∧ query < slots + 32 * c + 200 then
        (oracle.permutation (s3PermInput (s6GroupCallHead c state))).extractLsb' (8*(query-(slots + 32 * c))) 8
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s6_group_call_evaluation]
  rw [s3_reply_byte _ (slots + 32 * c) query _ (s6_group_ready_output c state slots pointer small) bound
    queryBound]
  by_cases inside : slots + 32 * c ≤ query ∧ query < slots + 32 * c + 200
  · rw [if_pos inside, if_pos inside]
  · rw [if_neg inside, if_neg inside]
    exact s3_byte_memory _ _ (s6_group_ready_memory c state) _

theorem s6_group_call_register (oracle : Oracle) (c : Nat) (state : MachineState) (reg : Reg)
    (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12) :
    (checkEvaluation oracle (s6GroupCall c state)).1.getReg reg = state.getReg reg := by
  rw [s6_group_call_evaluation]
  change (s3PermReply (s6GroupCallHead c state) _).getReg reg = _
  rw [s3_reply_register, s6_group_ready_register c state reg notInput notOutput]

/-- A group call changes only its 200-byte reply at the group's slot. -/
theorem s6_group_call_preserves (oracle : Oracle) (c : Nat) (state : MachineState)
    (slots address count : Nat) (pointer : state.getReg .x24 = BitVec.ofNat 64 slots) (small : c < 16)
    (bound : slots + 32 * c + 200 ≤ 2^64) (fits : address + count ≤ 2^64)
    (outside : address + count ≤ slots + 32 * c ∨ slots + 32 * c + 200 ≤ address) :
    readBuffer (checkEvaluation oracle (s6GroupCall c state)).1 address count =
      readBuffer state address count :=
  s3_read_congr _ _ _ _ count (fun i hi => by
    rw [s6_group_call_byte oracle c state slots _ pointer small bound (by omega), if_neg (by omega)])

/-- The window of a cell: 72 zero bytes, then the four digests. -/
theorem s6_cell_input (state : MachineState) (address : Nat) (d0 d1 d2 d3 : BitVec 256)
    (zero : (readBuffer state address 72).toNat = 0)
    (first : readBuffer state (address + 72) 32 = d0)
    (second : readBuffer state (address + 104) 32 = d1)
    (third : readBuffer state (address + 136) 32 = d2)
    (fourth : readBuffer state (address + 168) 32 = d3) :
    readBuffer state address 200 = s6GroupInput d0 d1 d2 d3 := by
  apply BitVec.eq_of_toNat_eq
  have a0 := s3_read_append state address 72 128 200 (address + 72) rfl rfl
  have a1 := s3_read_append state (address + 72) 32 96 128 (address + 104) rfl (by omega)
  have a2 := s3_read_append state (address + 104) 32 64 96 (address + 136) rfl (by omega)
  have a3 := s3_read_append state (address + 136) 32 32 64 (address + 168) rfl (by omega)
  have total : (readBuffer state address 200).toNat < 2^1600 := (readBuffer state address 200).isLt
  unfold s6GroupInput
  refine Eq.trans ?_ (BitVec.toNat_ofNat _ _).symm
  rw [a0, zero, a1, a2, a3, first, second, third, fourth] at total ⊢
  have e : 0 + 2^(8*72) * (d0.toNat + 2^(8*32) * (d1.toNat + 2^(8*32) * (d2.toNat + 2^(8*32) * d3.toNat))) =
      (d0.toNat + d1.toNat * 2^256 + d2.toNat * 2^512 + d3.toNat * 2^768) * 2^576 := by ring
  rw [e] at total ⊢
  exact (Nat.mod_eq_of_lt total).symm

/-- After the group call of a cell whose 72-byte prefix is zero, its slot holds the group digest
of the cell's four leaf digests. -/
theorem s6_cell_group (oracle : Oracle) (c : Nat) (state : MachineState) (cell slots : Nat)
    (d0 d1 d2 d3 : BitVec 256)
    (cellPointer : state.getReg (s6CellRegister c) = BitVec.ofNat 64 cell)
    (slotPointer : state.getReg .x24 = BitVec.ofNat 64 slots) (small : c < 16)
    (cellBound : cell + s6CellOffset c + 200 ≤ 2^64) (bound : slots + 32 * c + 200 ≤ 2^64)
    (zero : (readBuffer state (cell + s6CellOffset c) 72).toNat = 0)
    (first : readBuffer state (cell + s6CellOffset c + 72) 32 = d0)
    (second : readBuffer state (cell + s6CellOffset c + 104) 32 = d1)
    (third : readBuffer state (cell + s6CellOffset c + 136) 32 = d2)
    (fourth : readBuffer state (cell + s6CellOffset c + 168) 32 = d3) :
    readBuffer (checkEvaluation oracle (s6GroupCall c state)).1 (slots + 32 * c) 32 =
      s6GroupDigest oracle.permutation d0 d1 d2 d3 := by
  have input : s3PermInput (s6GroupCallHead c state) = s6GroupInput d0 d1 d2 d3 := by
    unfold s3PermInput
    rw [s6_group_ready_input c state cell cellPointer small, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), s3_read_memory _ _ (s6_group_ready_memory c state)]
    exact s6_cell_input state _ d0 d1 d2 d3 zero first second third fourth
  have read := read_serialized_slice (checkEvaluation oracle (s6GroupCall c state)).1
    (oracle.permutation (s3PermInput (s6GroupCallHead c state))) (slots + 32 * c) 0 32 (fun j hj => by
      rw [s6_group_call_byte oracle c state slots _ slotPointer small bound (by omega), if_pos (by omega),
        show slots + 32 * c + j - (slots + 32 * c) = 0 + j by omega])
  rw [read, input]
  unfold s6GroupDigest
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat]

end CommitGolfCandidate
