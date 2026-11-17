import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.NonceBuffer
import CommitGolfCandidate.CheckEvaluation

/-! Stage-3 leaf: byte-level effects of the leaf's stores, loads and syscall replies,
and the bytes of the state at the second permutation call. -/
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

theorem s3_read_zero (state : MachineState) (address count : Nat)
    (zero : ∀ i < count, state.getByte (BitVec.ofNat 64 (address+i)) = 0) :
    (readBuffer state address count).toNat = 0 := by
  unfold readBuffer
  rw [Finset.sum_eq_zero (fun i hi => by simp [zero i (Finset.mem_range.mp hi)])]
  simp

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

theorem s3_expand_nat (nonce : Nonce192) : (expandNonce192 nonce).toNat = nonce.toNat := by
  have bound : nonce.toNat < 2^256 := lt_trans nonce.isLt (by decide)
  change (BitVec.setWidth 256 nonce).toNat = nonce.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt bound]

/-! ### Instructions -/

theorem s3_address (pointer : Word) (base offset : Nat) (immediate : BitVec 12)
    (value : pointer = BitVec.ofNat 64 base)
    (extended : signExtend12 immediate = BitVec.ofNat 64 offset) :
    pointer + signExtend12 immediate = BitVec.ofNat 64 (base+offset) := by
  rw [value, extended, BitVec.ofNat_add]

/-- The four per-leaf immediates are nonnegative twelve-bit offsets. -/
theorem s3_unit_offset (u : Nat) (unit : u < 64) :
    signExtend12 (BitVec.ofNat 12 (24*u)) = BitVec.ofNat 64 (24*u) ∧
    signExtend12 (BitVec.ofNat 12 (24*u+8)) = BitVec.ofNat 64 (24*u+8) ∧
    signExtend12 (BitVec.ofNat 12 (24*u+16)) = BitVec.ofNat 64 (24*u+16) ∧
    signExtend12 (BitVec.ofNat 12 (32*u)) = BitVec.ofNat 64 (32*u) := by
  interval_cases u <;> exact ⟨rfl, rfl, rfl, rfl⟩

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

/-! ### Head: aim the first reply -/

theorem s3_head_memory (state : MachineState) : (s3LeafHead state).mem = state.mem := rfl

theorem s3_head_register (state : MachineState) (reg : Reg) (other : reg ≠ .x12) :
    (s3LeafHead state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl other | rfl

theorem s3_head_output (state : MachineState) :
    (s3LeafHead state).getReg .x12 = state.getReg .x10 + signExtend12 4032 := rfl

/-- The immediate -64: the first reply starts 64 bytes below the leaf. -/
theorem s3_head_below (base : Nat) (low : 64 ≤ base) :
    BitVec.ofNat 64 base + signExtend12 (4032 : BitVec 12) = BitVec.ofNat 64 (base - 64) := by
  rw [show signExtend12 (4032 : BitVec 12) = -(64 : Word) by decide]
  have equation : base = base - 64 + 64 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem s3_head_byte (state : MachineState) (address : Word) :
    (s3LeafHead state).getByte address = state.getByte address :=
  s3_byte_memory _ _ (s3_head_memory state) address

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

/-! ### Middle: nonce copy -/

theorem s3_mid_memory (u : Nat) (state : MachineState) :
    (s3LeafMid u state).mem =
      (s3CopyWord (s3CopyWord (s3CopyWord state
          (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (24*u)))
          (state.getReg .x10 + signExtend12 112))
          (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (24*u+8)))
          (state.getReg .x10 + signExtend12 120))
          (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (24*u+16)))
          (state.getReg .x10 + signExtend12 128)).mem := rfl

theorem s3_mid_register (u : Nat) (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x6) (notInput : reg ≠ .x10) (notOutput : reg ≠ .x12) :
    (s3LeafMid u state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl notScratch | exact absurd rfl notInput |
    exact absurd rfl notOutput

theorem s3_mid_input (u : Nat) (state : MachineState) :
    (s3LeafMid u state).getReg .x10 = state.getReg .x10 + signExtend12 56 := rfl

theorem s3_mid_output (u : Nat) (state : MachineState) :
    (s3LeafMid u state).getReg .x12 =
      state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (32*u)) := rfl

/-- The three copied words replace bytes 112..136 above the input pointer. -/
theorem s3_mid_byte (u : Nat) (state : MachineState) (base nonces query : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 base)
    (source : state.getReg .x18 = BitVec.ofNat 64 nonces)
    (unit : u < 64) (inputAligned : base % 8 = 0) (sourceAligned : nonces % 8 = 0)
    (inputBound : base + 136 ≤ 2^64) (sourceBound : nonces + 24*u + 24 ≤ 2^64)
    (separate : nonces + 24*u + 24 ≤ base + 112 ∨ base + 136 ≤ nonces + 24*u)
    (queryBound : query < 2^64) :
    (s3LeafMid u state).getByte (BitVec.ofNat 64 query) =
      if base + 112 ≤ query ∧ query < base + 136 then
        state.getByte (BitVec.ofNat 64 (nonces + 24*u + (query - (base+112))))
      else state.getByte (BitVec.ofNat 64 query) := by
  have offsets := s3_unit_offset u unit
  rw [s3_byte_memory _ _ (s3_mid_memory u state),
    s3_address _ nonces (24*u) _ source offsets.1,
    s3_address _ nonces (24*u+8) _ source offsets.2.1,
    s3_address _ nonces (24*u+16) _ source offsets.2.2.1,
    s3_address _ base 112 112 input rfl, s3_address _ base 120 120 input rfl,
    s3_address _ base 128 128 input rfl]
  have first (q : Nat) (hq : q < 2^64) :=
    s3_copy_byte state (nonces+24*u) (base+112) q (by omega) (by omega) (by omega) hq
  have second (q : Nat) (hq : q < 2^64) :=
    s3_copy_byte (s3CopyWord state (BitVec.ofNat 64 (nonces+24*u)) (BitVec.ofNat 64 (base+112)))
      (nonces+(24*u+8)) (base+120) q (by omega) (by omega) (by omega) hq
  rw [s3_copy_byte _ (nonces+(24*u+16)) (base+128) query (by omega) (by omega) (by omega)
    queryBound]
  by_cases high : base+128 ≤ query ∧ query < base+128+8
  · rw [if_pos high, second _ (by omega), if_neg (by omega), first _ (by omega),
      if_neg (by omega), if_pos (by omega)]
    exact s3_byte_address state _ _ (by omega)
  · rw [if_neg high, second query queryBound]
    by_cases middle : base+120 ≤ query ∧ query < base+120+8
    · rw [if_pos middle, first _ (by omega), if_neg (by omega), if_pos (by omega)]
      exact s3_byte_address state _ _ (by omega)
    · rw [if_neg middle, first query queryBound]
      by_cases low : base+112 ≤ query ∧ query < base+112+8
      · rw [if_pos low, if_pos (by omega)]
      · rw [if_neg low, if_neg (by omega)]

/-! ### Tail -/

theorem s3_tail_byte (state : MachineState) (address : Word) :
    (s3LeafTail state).getByte address = state.getByte address := rfl

theorem s3_tail_register (state : MachineState) (reg : Reg) (other : reg ≠ .x10) :
    (s3LeafTail state).getReg reg = state.getReg reg := by
  cases reg <;> first | rfl | exact absurd rfl other

/-! ### One leaf -/

/-- Reply of the first permutation call of a leaf. -/
def s3FirstReply (oracle : Oracle) (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  oracle.permutation (s3PermInput (s3LeafHead state))

/-- State at the second permutation call. -/
def s3MidState (oracle : Oracle) (u : Nat) (state : MachineState) : MachineState :=
  s3LeafMid u (s3PermReply (s3LeafHead state) (s3FirstReply oracle state))

/-- Reply of the second permutation call of a leaf. -/
def s3SecondReply (oracle : Oracle) (u : Nat) (state : MachineState) : BitVec PERMUTATION_WIDTH :=
  oracle.permutation (s3PermInput (s3MidState oracle u state))

/-- Fixed-oracle evaluation of one leaf: two forward permutation queries. -/
theorem s3_leaf_evaluation (oracle : Oracle) (u : Nat) (state : MachineState) :
    checkEvaluation oracle (s3Leaf u state) =
      (s3LeafTail (s3PermReply (s3MidState oracle u state) (s3SecondReply oracle u state)), 2) := by
  unfold s3Leaf
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem s3_leaf_queries (oracle : Oracle) (u : Nat) (state : MachineState) :
    (checkEvaluation oracle (s3Leaf u state)).2 = 2 := by
  rw [s3_leaf_evaluation]

/-- Addresses of one leaf. `base` is the address of the leaf value, the nonce is at
`nonces+24*u` and the heap slot at `slots+32*u`. The first reply covers
`[base-64, base+136)`. -/
structure S3LeafFrame (state : MachineState) (u base nonces slots : Nat) : Prop where
  input : state.getReg .x10 = BitVec.ofNat 64 base
  source : state.getReg .x18 = BitVec.ofNat 64 nonces
  heap : state.getReg .x23 = BitVec.ofNat 64 slots
  unit : u < 64
  low : 64 ≤ base
  inputAligned : base % 8 = 0
  sourceAligned : nonces % 8 = 0
  inputBound : base + 256 ≤ 2^64
  sourceBound : nonces + 24*u + 24 ≤ 2^64
  heapBound : slots + 32*u + 200 ≤ 2^64
  separate : nonces + 24*u + 24 + 64 ≤ base ∨ base + 136 ≤ nonces + 24*u

/-- Bytes at the second call: the nonce copy, the first reply, the rest untouched. -/
theorem s3_mid_state_byte (oracle : Oracle) (u : Nat) (state : MachineState)
    (base nonces slots query : Nat) (frame : S3LeafFrame state u base nonces slots)
    (queryBound : query < 2^64) :
    (s3MidState oracle u state).getByte (BitVec.ofNat 64 query) =
      if base+112 ≤ query ∧ query < base+136 then
        state.getByte (BitVec.ofNat 64 (nonces+24*u+(query-(base+112))))
      else if base-64 ≤ query ∧ query < base-64+200 then
        (s3FirstReply oracle state).extractLsb' (8*(query-(base-64))) 8
      else state.getByte (BitVec.ofNat 64 query) := by
  obtain ⟨input, source, heap, unit, low, inputAligned, sourceAligned, inputBound, sourceBound,
    heapBound, separate⟩ := frame
  have headInput : (s3LeafHead state).getReg .x10 = BitVec.ofNat 64 base :=
    (s3_head_register state .x10 (by decide)).trans input
  have headOutput : (s3LeafHead state).getReg .x12 = BitVec.ofNat 64 (base-64) := by
    rw [s3_head_output, input]
    exact s3_head_below base low
  have reply (q : Nat) (hq : q < 2^64) :=
    s3_reply_byte (s3LeafHead state) (base-64) q (s3FirstReply oracle state) headOutput
      (by omega) hq
  unfold s3MidState
  rw [s3_mid_byte u _ base nonces query
    ((s3_reply_register _ _ .x10).trans headInput)
    ((s3_reply_register _ _ .x18).trans
      ((s3_head_register state .x18 (by decide)).trans source))
    unit inputAligned sourceAligned (by omega) sourceBound (by omega) queryBound]
  by_cases copied : base+112 ≤ query ∧ query < base+136
  · rw [if_pos copied, if_pos copied, reply _ (by omega), if_neg (by omega), s3_head_byte]
  · rw [if_neg copied, if_neg copied, reply query queryBound]
    by_cases written : base-64 ≤ query ∧ query < base-64+200
    · rw [if_pos written, if_pos written]
    · rw [if_neg written, if_neg written, s3_head_byte]

end CommitGolfCandidate
