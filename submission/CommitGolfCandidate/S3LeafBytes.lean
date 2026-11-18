import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.S6Tree
import CommitGolfCandidate.NonceBuffer
import CommitGolfCandidate.CheckEvaluation

/-! Commitment leaf: byte-level effects of the leaf's loads, stores and syscall replies, and the
bytes of the state at the second permutation call. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option exponentiation.threshold 4096

/-! ### Bytes -/

/-- A byte read only depends on memory. -/
theorem s3_byte_memory (left right : MachineState) (same : left.mem = right.mem) (address : Word) :
    left.getByte address = right.getByte address := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem s3_byte_address (state : MachineState) (left right : Nat) (same : left = right) :
    state.getByte (BitVec.ofNat 64 left) = state.getByte (BitVec.ofNat 64 right) := by
  rw [same]

/-- A byte is the indexed part of its aligned doubleword. -/
theorem s3_byte_word (state : MachineState) (query : Nat) :
    state.getByte (BitVec.ofNat 64 query) =
      extractByte (state.getMem (BitVec.ofNat 64 (8*(query/8)))) (query%8) := by
  have h := aligned_byte state (query/8) (query%8) (by omega)
  have e1 : 8*(query/8) + query%8 = query := by omega
  have e2 : 8*(query/8) + 8*(query%8/8) = 8*(query/8) := by omega
  have e3 : query%8%8 = query%8 := by omega
  rw [e1, e2, e3] at h
  exact h

/-- An aligned doubleword store changes exactly its eight bytes. -/
theorem s3_store_byte (state : MachineState) (destination : Nat) (value : Word) (query : Nat)
    (aligned : destination % 8 = 0) (bound : destination + 8 ≤ 2^64) (queryBound : query < 2^64) :
    (state.setMem (BitVec.ofNat 64 destination) value).getByte (BitVec.ofNat 64 query) =
      if destination ≤ query ∧ query < destination + 8 then extractByte value (query - destination)
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_word (state.setMem (BitVec.ofNat 64 destination) value), s3_byte_word state]
  by_cases inside : destination ≤ query ∧ query < destination + 8
  · have same : 8*(query/8) = destination := by omega
    have offset : query % 8 = query - destination := by omega
    rw [if_pos inside, same, MachineState.getMem_setMem_eq, offset]
  · have different : BitVec.ofNat 64 (8*(query/8)) ≠ BitVec.ofNat 64 destination := by
      intro equal
      have natural := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8*(query/8) < 2^64),
        Nat.mod_eq_of_lt (by omega : destination < 2^64)] at natural
      omega
    rw [if_neg inside, MachineState.getMem_setMem_ne different]

/-- The bytes of a loaded doubleword are the bytes at its aligned address. -/
theorem s3_load_byte (state : MachineState) (source offset : Nat)
    (aligned : source % 8 = 0) (inside : offset < 8) :
    extractByte (state.getMem (BitVec.ofNat 64 source)) offset =
      state.getByte (BitVec.ofNat 64 (source+offset)) := by
  rw [s3_byte_word state (source+offset)]
  have word : 8*((source+offset)/8) = source := by omega
  have position : (source+offset)%8 = offset := by omega
  rw [word, position]

/-- A syscall reply changes exactly its output bytes. -/
theorem s3_write_byte {bits : Nat} (state : MachineState) (destination bytes : Nat)
    (answer : BitVec bits) (query : Nat) (size : (bits+7)/8 = bytes)
    (bound : destination + bytes ≤ 2^64) (queryBound : query < 2^64) :
    (writeBits state (BitVec.ofNat 64 destination) answer).getByte (BitVec.ofNat 64 query) =
      if destination ≤ query ∧ query < destination + bytes then
        answer.extractLsb' (8*(query-destination)) 8
      else state.getByte (BitVec.ofNat 64 query) := by
  subst size
  by_cases inside : destination ≤ query ∧ query < destination + (bits+7)/8
  · rw [if_pos inside]
    have written := write_bits_byte state (BitVec.ofNat 64 destination) answer (query-destination)
      (by omega) (by omega)
    rw [← BitVec.ofNat_add, show destination + (query-destination) = query by omega] at written
    exact written
  · rw [if_neg inside]
    apply write_bits_byte_outside
    intro i hi equal
    have natural := congrArg BitVec.toNat equal
    rw [← BitVec.ofNat_add] at natural
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt queryBound,
      Nat.mod_eq_of_lt (by omega : destination+i < 2^64)] at natural
    omega

/-! ### Buffers -/

theorem s3_read_address (state : MachineState) (left right count : Nat) (same : left = right) :
    readBuffer state left count = readBuffer state right count := by
  rw [same]

/-- Buffers with equal bytes are equal. -/
theorem s3_read_congr (left right : MachineState) (leftAddress rightAddress count : Nat)
    (same : ∀ i < count, left.getByte (BitVec.ofNat 64 (leftAddress+i)) =
      right.getByte (BitVec.ofNat 64 (rightAddress+i))) :
    readBuffer left leftAddress count = readBuffer right rightAddress count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  rw [same i (Finset.mem_range.mp hi)]

theorem s3_read_memory (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count :=
  s3_read_congr left right address address count (fun _ _ => s3_byte_memory left right same _)

/-- A buffer is its low part plus the shifted high part. -/
theorem s3_read_append (state : MachineState) (address left right total middle : Nat)
    (size : left+right = total) (next : address+left = middle) :
    (readBuffer state address total).toNat =
      (readBuffer state address left).toNat +
        2^(8*left) * (readBuffer state middle right).toNat := by
  subst size
  subst next
  have low : (readBuffer state address (left+right)).extractLsb' (8*0) (8*left) =
      readBuffer state address left := by
    have slice := read_buffer_slice state address (left+right) 0 left (by omega)
    rwa [Nat.add_zero] at slice
  have high := read_buffer_slice state address (left+right) left right (by omega)
  have lowNat := congrArg BitVec.toNat low
  have highNat := congrArg BitVec.toNat high
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one] at lowNat highNat
  have bound : (readBuffer state address (left+right)).toNat < 2^(8*left) * 2^(8*right) := by
    have limit := (readBuffer state address (left+right)).isLt
    have power : 2^(8*(left+right)) = 2^(8*left) * 2^(8*right) := by
      rw [Nat.mul_add, Nat.pow_add]
    exact lt_of_lt_of_eq limit power
  rw [← lowNat, ← highNat, Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul bound)]
  exact (Nat.mod_add_div _ _).symm

theorem s3_split_low (low high power : Nat) (small : low < power) :
    (low + power * high) % power = low := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small]

theorem s3_split_high (low high power : Nat) (small : low < power) :
    (low + power * high) / power = high := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt small, Nat.zero_add]

/-! ### Instructions -/

theorem s3_address (pointer : Word) (base offset : Nat) (immediate : BitVec 12)
    (value : pointer = BitVec.ofNat 64 base)
    (extended : signExtend12 immediate = BitVec.ofNat 64 offset) :
    pointer + signExtend12 immediate = BitVec.ofNat 64 (base+offset) := by
  rw [value, extended, BitVec.ofNat_add]


/-- A twelve-bit immediate below 2048 is a nonnegative offset. -/
theorem s3_offset_extend (offset : Nat) (small : offset < 2048) :
    signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset := by
  have msb : (BitVec.ofNat 12 offset).msb = false := by
    rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not, not_le]
    omega
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- Memory effect of one load/store pair. -/
def s3CopyWord (state : MachineState) (source destination : Word) : MachineState :=
  state.setMem destination (state.getMem source)

theorem s3_copy_byte (state : MachineState) (source destination query : Nat)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (bound : destination + 8 ≤ 2^64) (queryBound : query < 2^64) :
    (s3CopyWord state (BitVec.ofNat 64 source) (BitVec.ofNat 64 destination)).getByte
        (BitVec.ofNat 64 query) =
      if destination ≤ query ∧ query < destination + 8 then
        state.getByte (BitVec.ofNat 64 (source + (query - destination)))
      else state.getByte (BitVec.ofNat 64 query) := by
  unfold s3CopyWord
  rw [s3_store_byte state destination _ query destinationAligned bound queryBound]
  by_cases inside : destination ≤ query ∧ query < destination + 8
  · rw [if_pos inside, if_pos inside, s3_load_byte state source _ sourceAligned (by omega)]
  · rw [if_neg inside, if_neg inside]

/-! ### Cells and slots -/

/-- Offset of leaf `l`'s digest slot from the base register of its cell. -/
def s6SlotOffset (l : Nat) : Nat := s6CellOffset (l / 4) + 72 + 32 * (l % 4)

/-- Value of the base register of cell `c` above the block's first cell. -/
def s6CellShift (c : Nat) : Nat := if c < 5 then 0 else if c < 10 then 1840 else 3680

theorem s6_cell_address_sum (c : Nat) (small : c < 16) : s6CellShift c + s6CellOffset c = 368 * c := by
  unfold s6CellShift s6CellOffset
  split_ifs <;> omega

theorem s6_cell_offset (c : Nat) (small : c < 16) : s6CellOffset c ≤ 1840 ∧ s6CellOffset c % 8 = 0 := by
  unfold s6CellOffset
  split_ifs <;> omega

theorem s6_slot_offset (l : Nat) (unit : l < 64) : s6SlotOffset l ≤ 2008 ∧ s6SlotOffset l % 8 = 0 := by
  have cell := s6_cell_offset (l / 4) (by omega)
  unfold s6SlotOffset
  omega

theorem s6_slot_address (l : Nat) (unit : l < 64) :
    s6CellShift (l / 4) + s6SlotOffset l = 368 * (l / 4) + 72 + 32 * (l % 4) := by
  have cell := s6_cell_address_sum (l / 4) (by omega)
  unfold s6SlotOffset
  omega

/-! ### Head: nonce copy, tag, first reply pointer -/

theorem s3_head_memory (l : Nat) (state : MachineState) :
    (s3LeafHead l state).mem =
      ((s3CopyWord (s3CopyWord state
          (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (16*l)))
          (state.getReg .x10 + signExtend12 0))
          (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (16*l+8)))
          (state.getReg .x10 + signExtend12 8)).setMem
        (state.getReg .x10 + signExtend12 16) (state.getReg .x10)).mem := rfl

theorem s3_head_register (l : Nat) (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x6) (notOutput : reg ≠ .x12) :
    (s3LeafHead l state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl notScratch | exact absurd rfl notOutput | rfl

/-- The head aims the first reply 56 bytes below the window (the immediate 4040 is -56). -/
theorem s3_head_output (l : Nat) (state : MachineState) (base : Nat)
    (pointer : state.getReg .x10 = BitVec.ofNat 64 base) (low : 56 ≤ base) :
    (s3LeafHead l state).getReg .x12 = BitVec.ofNat 64 (base - 56) := by
  change state.getReg .x10 + signExtend12 (BitVec.ofNat 12 4040) = _
  rw [pointer, show signExtend12 (BitVec.ofNat 12 4040) = BitVec.ofNat 64 (2^64 - 56) from rfl,
    ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- Bytes after the head: the nonce at `[base, base + 16)`, the tag `base` at `[base + 16, base + 24)`. -/
theorem s3_head_byte (l : Nat) (state : MachineState) (base nonces query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 base)
    (source : state.getReg .x18 = BitVec.ofNat 64 nonces)
    (unit : l < 64) (inputAligned : base % 8 = 0) (sourceAligned : nonces % 8 = 0)
    (inputBound : base + 24 ≤ 2^64) (sourceBound : nonces + 16*l + 16 ≤ 2^64)
    (separate : nonces + 16*l + 16 ≤ base ∨ base + 24 ≤ nonces + 16*l)
    (queryBound : query < 2^64) :
    (s3LeafHead l state).getByte (BitVec.ofNat 64 query) =
      if base ≤ query ∧ query < base + 16 then
        state.getByte (BitVec.ofNat 64 (nonces + 16*l + (query - base)))
      else if base + 16 ≤ query ∧ query < base + 24 then
        extractByte (BitVec.ofNat 64 base) (query - (base + 16))
      else state.getByte (BitVec.ofNat 64 query) := by
  rw [s3_byte_memory _ _ (s3_head_memory l state),
    s3_address _ nonces (16*l) _ source (s3_offset_extend _ (by omega)),
    s3_address _ nonces (16*l+8) _ source (s3_offset_extend _ (by omega)),
    s3_address _ base 0 0 input rfl, s3_address _ base 8 8 input rfl,
    s3_address _ base 16 16 input rfl, input]
  have first (q : Nat) (hq : q < 2^64) :=
    s3_copy_byte state (nonces+16*l) (base+0) q (by omega) (by omega) (by omega) hq
  have second (q : Nat) (hq : q < 2^64) :=
    s3_copy_byte (s3CopyWord state (BitVec.ofNat 64 (nonces+16*l)) (BitVec.ofNat 64 (base+0)))
      (nonces+(16*l+8)) (base+8) q (by omega) (by omega) (by omega) hq
  rw [s3_store_byte _ (base+16) _ query (by omega) (by omega) queryBound]
  by_cases tag : base+16 ≤ query ∧ query < base+16+8
  · rw [if_pos tag, if_neg (by omega), if_pos (by omega)]
  · rw [if_neg tag, second query queryBound]
    by_cases high : base+8 ≤ query ∧ query < base+8+8
    · rw [if_pos high, first _ (by omega), if_neg (by omega), if_pos (by omega)]
      exact s3_byte_address state _ _ (by omega)
    · rw [if_neg high, first query queryBound]
      by_cases low : base+0 ≤ query ∧ query < base+0+8
      · rw [if_pos low, if_pos (by omega)]
        exact s3_byte_address state _ _ (by omega)
      · rw [if_neg low, if_neg (by omega), if_neg (by omega)]

/-! ### Replies -/

theorem s3_reply_register (state : MachineState) (answer : BitVec PERMUTATION_WIDTH) (reg : Reg) :
    (s3PermReply state answer).getReg reg = state.getReg reg :=
  writeBits_register state _ answer reg

theorem s3_reply_byte (state : MachineState) (destination query : Nat)
    (answer : BitVec PERMUTATION_WIDTH)
    (pointer : state.getReg .x12 = BitVec.ofNat 64 destination)
    (bound : destination + 200 ≤ 2^64) (queryBound : query < 2^64) :
    (s3PermReply state answer).getByte (BitVec.ofNat 64 query) =
      if destination ≤ query ∧ query < destination + 200 then
        answer.extractLsb' (8*(query-destination)) 8
      else state.getByte (BitVec.ofNat 64 query) := by
  unfold s3PermReply
  rw [pointer]
  exact s3_write_byte state destination 200 answer query rfl bound queryBound

/-! ### Middle and tail -/

theorem s3_mid_byte (l : Nat) (state : MachineState) (address : Word) :
    (s3LeafMid l state).getByte address = state.getByte address := rfl

theorem s3_mid_register (l : Nat) (state : MachineState) (reg : Reg)
    (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12) :
    (s3LeafMid l state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl notInput | exact absurd rfl notOutput | rfl

theorem s3_mid_input (l : Nat) (state : MachineState) :
    (s3LeafMid l state).getReg .x10 = state.getReg .x10 + signExtend12 80 := rfl

theorem s3_mid_output (l : Nat) (state : MachineState) :
    (s3LeafMid l state).getReg .x12 =
      state.getReg (s6CellRegister (l / 4)) + signExtend12 (BitVec.ofNat 12 (s6SlotOffset l)) := by
  have base : s6CellRegister (l / 4) ≠ .x10 := by
    unfold s6CellRegister
    split_ifs <;> decide
  show ((state.setReg .x10 (state.getReg .x10 + signExtend12 80)).setPC (state.pc + 4)).getReg
      (s6CellRegister (l / 4)) + _ = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm base)]
  rfl

theorem s3_tail_byte (l : Nat) (state : MachineState) (address : Word) :
    (s3LeafTail l state).getByte address = state.getByte address := by
  unfold s3LeafTail s3LeafTailInstruction s3LeafNextRegister
  split_ifs <;> rfl

theorem s3_tail_register (l : Nat) (state : MachineState) (reg : Reg) (other : reg ≠ s3LeafNextRegister l) :
    (s3LeafTail l state).getReg reg = state.getReg reg := by
  show ((state.setReg (s3LeafNextRegister l) (state.getReg .x10 + signExtend12 176)).setPC (state.pc + 4)).getReg
    reg = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm other)]

theorem s3_tail_link (l : Nat) (state : MachineState) :
    (s3LeafTail l state).getReg (s3LeafNextRegister l) = state.getReg .x10 + signExtend12 176 := by
  have notZero : s3LeafNextRegister l ≠ .x0 := by
    unfold s3LeafNextRegister
    split_ifs <;> decide
  show ((state.setReg (s3LeafNextRegister l) (state.getReg .x10 + signExtend12 176)).setPC (state.pc + 4)).getReg
    (s3LeafNextRegister l) = _
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq notZero]

/-! ### One leaf -/

/-- Reply of the first permutation call of a leaf. -/
def s3FirstReply (oracle : Oracle) (l : Nat) (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  oracle.permutation (s3PermInput (s3LeafHead l state))

/-- State at the second permutation call. -/
def s3MidState (oracle : Oracle) (l : Nat) (state : MachineState) : MachineState :=
  s3LeafMid l (s3PermReply (s3LeafHead l state) (s3FirstReply oracle l state))

/-- Reply of the second permutation call of a leaf. -/
def s3SecondReply (oracle : Oracle) (l : Nat) (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  oracle.permutation (s3PermInput (s3MidState oracle l state))

/-- Fixed-oracle evaluation of one leaf: two forward permutation queries. -/
theorem s3_leaf_evaluation (oracle : Oracle) (l : Nat) (state : MachineState) :
    checkEvaluation oracle (s3Leaf l state) =
      (s3LeafTail l (s3PermReply (s3MidState oracle l state) (s3SecondReply oracle l state)), 2) := by
  unfold s3Leaf
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem s3_leaf_queries (oracle : Oracle) (l : Nat) (state : MachineState) :
    (checkEvaluation oracle (s3Leaf l state)).2 = 2 := by
  rw [s3_leaf_evaluation]

/-- Addresses of leaf `l` of a block. `base` is x10 at leaf entry (the leaf's entry minus 24); the
first reply covers `[base - 56, base + 144)`, the nonce is at `nonces + 16 l`, and the digest slot
at `cell + s6SlotOffset l`, where `cell` is the value of the cell's base register. -/
structure S3LeafFrame (state : MachineState) (l base nonces cell : Nat) : Prop where
  input : state.getReg .x10 = BitVec.ofNat 64 base
  source : state.getReg .x18 = BitVec.ofNat 64 nonces
  cellPointer : state.getReg (s6CellRegister (l / 4)) = BitVec.ofNat 64 cell
  unit : l < 64
  inputAligned : base % 8 = 0
  sourceAligned : nonces % 8 = 0
  cellAligned : cell % 8 = 0
  inputLow : 56 ≤ base
  inputBound : base + 280 ≤ 2^64
  sourceBound : nonces + 16*l + 16 ≤ 2^64
  cellBound : cell + s6SlotOffset l + 200 ≤ 2^64
  separate : nonces + 16*l + 16 ≤ base - 56 ∨ base + 280 ≤ nonces + 16*l

/-- Bytes at the second call: the first reply, then the head's stores, the rest untouched. -/
theorem s3_mid_state_byte (oracle : Oracle) (l : Nat) (state : MachineState)
    (base nonces cell query : Nat) (frame : S3LeafFrame state l base nonces cell)
    (queryBound : query < 2^64) :
    (s3MidState oracle l state).getByte (BitVec.ofNat 64 query) =
      if base-56 ≤ query ∧ query < base+144 then
        (s3FirstReply oracle l state).extractLsb' (8*(query-(base-56))) 8
      else state.getByte (BitVec.ofNat 64 query) := by
  have headOutput : (s3LeafHead l state).getReg .x12 = BitVec.ofNat 64 (base-56) :=
    s3_head_output l state base frame.input frame.inputLow
  have inputBound := frame.inputBound
  have inputLow := frame.inputLow
  have separate := frame.separate
  have sourceBound := frame.sourceBound
  unfold s3MidState
  rw [s3_mid_byte, s3_reply_byte (s3LeafHead l state) (base-56) query _ headOutput (by omega)
    queryBound]
  by_cases written : base-56 ≤ query ∧ query < base+144
  · rw [if_pos written, if_pos (by omega)]
  · rw [if_neg written, if_neg (by omega),
      s3_head_byte l state base nonces query frame.input frame.source frame.unit frame.inputAligned
        frame.sourceAligned (by omega) frame.sourceBound (by omega) queryBound,
      if_neg (by omega), if_neg (by omega)]

end CommitGolfCandidate
