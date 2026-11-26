import CommitGolfCandidate.WriteMemoryCore

/-! Halfword loads and stores (stage D2): byte-exact effects of `LHU`/`SH` at 2-aligned
addresses, and a generic straight-line halfword copy (`LHU x6, a(src)` / `SH x6, b(dst)`
pairs) with its exact byte semantics and interpreter execution. -/
namespace CommitGolfCandidate.CKBHalf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem half_offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem half_address_decomposition (address : Word) :
    alignToDword address + BitVec.ofNat 64 (byteOffset address) = address := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (address &&& ~~~7#64) &&& (address &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  have combined : (address &&& ~~~7#64) ||| (address &&& 7#64) = address := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]

/-- Byte offset of a natural-number address. -/
theorem nat_byte_offset (address : Nat) : byteOffset (BitVec.ofNat 64 address) = address % 8 := by
  rw [half_offset_mod, BitVec.toNat_ofNat]
  omega

/-- Doubleword base of a natural-number address. -/
theorem nat_align_dword (address : Nat) :
    alignToDword (BitVec.ofNat 64 address) = BitVec.ofNat 64 (8 * (address / 8)) := by
  have parts := half_address_decomposition (BitVec.ofNat 64 address)
  rw [nat_byte_offset] at parts
  have joined : BitVec.ofNat 64 (8 * (address / 8)) + BitVec.ofNat 64 (address % 8) =
      BitVec.ofNat 64 address := by
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 (address % 8))
    (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using canceled

/-- Every byte read, as a byte of its doubleword. -/
theorem nat_get_byte (state : MachineState) (address : Nat) :
    state.getByte (BitVec.ofNat 64 address) =
      extractByte (state.getMem (BitVec.ofNat 64 (8 * (address / 8)))) (address % 8) := by
  simp only [MachineState.getByte, nat_align_dword, nat_byte_offset]

/-! ### Bit-level facts about the interpreter's word operations -/

theorem extract_byte_getLsbD (word : Word) (pos i : Nat) (inside : i < 8) :
    (extractByte word pos).getLsbD i = word.getLsbD (pos * 8 + i) := by
  simp [extractByte, BitVec.truncate_eq_setWidth, inside]

theorem extract_half_getLsbD (word : Word) (pos i : Nat) (inside : i < 16) :
    (extractHalfword word pos).getLsbD i = word.getLsbD (pos * 16 + i) := by
  simp [extractHalfword, BitVec.truncate_eq_setWidth, inside]

private theorem mask_getLsbD (j : Nat) : (0xFFFF#64).getLsbD j = decide (j < 16) := by
  rw [BitVec.getLsbD_ofNat, show (0xFFFF : Nat) = 2^16 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 16
  · simp [h, show j < 64 by omega]
  · simp [h]

theorem replace_half_getLsbD (word : Word) (pos : Nat) (half : BitVec 16) (i : Nat)
    (inside : i < 64) :
    (replaceHalfword word pos half).getLsbD i =
      if pos * 16 ≤ i ∧ i < pos * 16 + 16 then half.getLsbD (i - pos * 16) else word.getLsbD i := by
  simp only [replaceHalfword, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, mask_getLsbD, BitVec.getLsbD_setWidth]
  by_cases low : i < pos * 16
  · rw [if_neg (by omega)]
    simp [low, inside]
  · by_cases high : i < pos * 16 + 16
    · rw [if_pos (by omega)]
      have small : i - pos * 16 < 16 := by omega
      simp [low, inside, small, show i - pos * 16 < 64 by omega]
    · rw [if_neg (by omega)]
      have big : ¬ (i - pos * 16 < 16) := by omega
      simp [low, inside, big, BitVec.getLsbD_of_ge half (i - pos * 16) (by omega)]

theorem half_eq_bytes (word : Word) (pos : Nat) :
    extractHalfword word pos = extractByte word (2 * pos + 1) ++ extractByte word (2 * pos) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [extract_half_getLsbD _ _ _ inside, BitVec.getLsbD_append]
  by_cases low : i < 8
  · simp only [low, decide_true, Bool.cond_true]
    rw [extract_byte_getLsbD word (2 * pos) i low]
    congr 1
    omega
  · simp only [low, decide_false, Bool.cond_false]
    rw [extract_byte_getLsbD word (2 * pos + 1) (i - 8) (by omega)]
    congr 1
    omega

theorem extract_replace_half (word : Word) (pos : Nat) (half : BitVec 16) (r : Nat)
    (posBound : pos < 4) (rBound : r < 8) :
    extractByte (replaceHalfword word pos half) r =
      if r = 2 * pos then half.extractLsb' 0 8
      else if r = 2 * pos + 1 then half.extractLsb' 8 8
      else extractByte word r := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [extract_byte_getLsbD _ _ _ inside, replace_half_getLsbD _ _ _ _ (by omega)]
  by_cases low : r = 2 * pos
  · rw [if_pos (by omega), if_pos low, BitVec.getLsbD_extractLsb']
    simp only [inside, decide_true, Bool.true_and]
    congr 1
    omega
  · by_cases high : r = 2 * pos + 1
    · rw [if_pos (by omega), if_neg low, if_pos high, BitVec.getLsbD_extractLsb']
      simp only [inside, decide_true, Bool.true_and]
      congr 1
      omega
    · rw [if_neg (by omega), if_neg low, if_neg high, extract_byte_getLsbD _ _ _ inside]

/-! ### Memory-level halfword facts (natural-number addresses) -/

/-- A halfword load at an even address returns its two little-endian bytes. -/
theorem get_halfword_eq (state : MachineState) (address : Nat) (even : address % 2 = 0) :
    state.getHalfword (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 (address + 1)) ++ state.getByte (BitVec.ofNat 64 address) := by
  have nextBase : (address + 1) / 8 = address / 8 := by omega
  simp only [MachineState.getHalfword, nat_align_dword, nat_byte_offset]
  rw [nat_get_byte, nat_get_byte, nextBase, half_eq_bytes,
    show 2 * (address % 8 / 2) + 1 = (address + 1) % 8 by omega,
    show 2 * (address % 8 / 2) = address % 8 by omega]

/-- The same fact on natural numbers. -/
theorem get_halfword_bytes (state : MachineState) (address : Nat) (even : address % 2 = 0) :
    (state.getHalfword (BitVec.ofNat 64 address)).toNat =
      (state.getByte (BitVec.ofNat 64 address)).toNat +
        256 * (state.getByte (BitVec.ofNat 64 (address+1))).toNat := by
  rw [get_halfword_eq state address even, BitVec.toNat_append]
  have := (state.getByte (BitVec.ofNat 64 address)).isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt this, Nat.shiftLeft_eq]
  omega

private theorem word_index_ne (left right : Nat) (leftBound : left < 2^64) (rightBound : right < 2^64)
    (different : left / 8 ≠ right / 8) :
    BitVec.ofNat 64 (8 * (left / 8)) ≠ BitVec.ofNat 64 (8 * (right / 8)) := by
  intro same
  have := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- A halfword store at an even address changes exactly its two bytes. Addresses are
below 2^64, so distinct naturals are distinct machine addresses. -/
theorem set_halfword_get_byte (state : MachineState) (address query : Nat) (half : BitVec 16)
    (even : address % 2 = 0) (addressBound : address < 2^64) (queryBound : query < 2^64) :
    (state.setHalfword (BitVec.ofNat 64 address) half).getByte (BitVec.ofNat 64 query) =
      if query = address then half.extractLsb' 0 8
      else if query = address + 1 then half.extractLsb' 8 8
      else state.getByte (BitVec.ofNat 64 query) := by
  simp only [MachineState.setHalfword, nat_align_dword, nat_byte_offset]
  rw [nat_get_byte, nat_get_byte]
  by_cases sameWord : query / 8 = address / 8
  · rw [sameWord, MachineState.getMem_setMem_eq,
      extract_replace_half _ _ _ _ (by omega) (by omega)]
    by_cases low : query = address
    · rw [if_pos (by omega), if_pos low]
    · by_cases high : query = address + 1
      · rw [if_neg (by omega), if_pos (by omega), if_neg low, if_pos high]
      · rw [if_neg (by omega), if_neg (by omega), if_neg low, if_neg high]
  · rw [MachineState.getMem_setMem_ne (word_index_ne _ _ queryBound addressBound sameWord),
      if_neg (by omega), if_neg (by omega)]

/-- The natural-number form of `set_halfword_get_byte`. -/
theorem set_halfword_byte (state : MachineState) (address query : Nat) (half : BitVec 16)
    (even : address % 2 = 0) (addressBound : address < 2^64) (queryBound : query < 2^64) :
    ((state.setHalfword (BitVec.ofNat 64 address) half).getByte (BitVec.ofNat 64 query)).toNat =
      if query = address then half.toNat % 256
      else if query = address + 1 then half.toNat / 256
      else (state.getByte (BitVec.ofNat 64 query)).toNat := by
  rw [set_halfword_get_byte state address query half even addressBound queryBound]
  split
  · simp [BitVec.extractLsb'_toNat]
  · split
    · simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
      have := half.isLt
      omega
    · rfl

/-- A halfword store leaves every doubleword in a different 8-byte block unchanged. -/
theorem set_halfword_get_mem (state : MachineState) (address word : Nat) (half : BitVec 16)
    (aligned : word % 8 = 0) (addressBound : address < 2^64) (wordBound : word < 2^64)
    (different : word / 8 ≠ address / 8) :
    (state.setHalfword (BitVec.ofNat 64 address) half).getMem (BitVec.ofNat 64 word) =
      state.getMem (BitVec.ofNat 64 word) := by
  simp only [MachineState.setHalfword, nat_align_dword, nat_byte_offset]
  apply MachineState.getMem_setMem_ne
  have := word_index_ne word address wordBound addressBound different
  rwa [show 8 * (word / 8) = word by omega] at this

/-- Reads agree when all bytes agree. -/
theorem read_buffer_bytes_congr (left right : MachineState) (first second count : Nat)
    (bytes : ∀ i < count, left.getByte (BitVec.ofNat 64 (first + i)) =
      right.getByte (BitVec.ofNat 64 (second + i))) :
    readBuffer left first count = readBuffer right second count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro i inside
  rw [bytes i (Finset.mem_range.mp inside)]

/-! ### Straight-line halfword copies

`halfRun src dst state a b k` executes `k` pairs `LHU x6, (a+2j)(src)` /
`SH x6, (b+2j)(dst)` for `j < k`. Only `x6` and the PC change. -/

/-- One halfword copy pair. -/
def halfStep (src dst : Reg) (state : MachineState) (a b : Nat) : MachineState :=
  execInstrBr (execInstrBr state (.LHU .x6 src (BitVec.ofNat 12 a))) (.SH dst .x6 (BitVec.ofNat 12 b))

/-- `k` consecutive halfword copy pairs with source offset `a` and destination offset `b`. -/
def halfRun (src dst : Reg) (state : MachineState) (a b : Nat) : Nat → MachineState
  | 0 => state
  | k + 1 => halfStep src dst (halfRun src dst state a b k) (a + 2 * k) (b + 2 * k)

theorem half_offset (offset : Nat) (bounded : offset < 2048) :
    signExtend12 (BitVec.ofNat 12 offset) = BitVec.ofNat 64 offset := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega

theorem half_step_register (src dst : Reg) (state : MachineState) (a b : Nat) (reg : Reg)
    (scratch : reg ≠ .x6) :
    (halfStep src dst state a b).getReg reg = state.getReg reg := by
  simp only [halfStep, execInstrBr, MachineState.getReg_setPC]
  rw [show ∀ (t : MachineState) (address : Word) (h : BitVec 16),
      (t.setHalfword address h).getReg reg = t.getReg reg from fun t address h => by
        cases reg <;> rfl]
  exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)

theorem half_step_pc (src dst : Reg) (state : MachineState) (a b : Nat) :
    (halfStep src dst state a b).pc = state.pc + 8 := by
  simp only [halfStep, execInstrBr, MachineState.setPC]
  rw [BitVec.add_assoc]
  rfl

theorem half_run_register (src dst : Reg) (state : MachineState) (a b k : Nat) (reg : Reg)
    (scratch : reg ≠ .x6) :
    (halfRun src dst state a b k).getReg reg = state.getReg reg := by
  induction k with
  | zero => rfl
  | succ k ih => rw [halfRun, half_step_register _ _ _ _ _ _ scratch, ih]

theorem half_run_pc (src dst : Reg) (state : MachineState) (a b k : Nat) :
    (halfRun src dst state a b k).pc = state.pc + BitVec.ofNat 64 (8 * k) := by
  induction k with
  | zero => simp [halfRun]
  | succ k ih =>
    rw [halfRun, half_step_pc, ih, BitVec.add_assoc]
    congr 1
    rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
    congr 1

private theorem append_low (x y : BitVec 8) : (x ++ y).extractLsb' 0 8 = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [inside]

private theorem append_high (x y : BitVec 8) : (x ++ y).extractLsb' 8 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp [inside]

/-- Exact byte effect of one copy pair. -/
theorem half_step_byte (src dst : Reg) (state : MachineState) (a b S D query : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : state.getReg src = BitVec.ofNat 64 S) (target : state.getReg dst = BitVec.ofNat 64 D)
    (aBound : a < 2048) (bBound : b < 2048)
    (sourceEven : (S + a) % 2 = 0) (targetEven : (D + b) % 2 = 0)
    (sourceBound : S + a + 2 ≤ 2^64) (targetBound : D + b + 2 ≤ 2^64) (queryBound : query < 2^64) :
    (halfStep src dst state a b).getByte (BitVec.ofNat 64 query) =
      if query = D + b then state.getByte (BitVec.ofNat 64 (S + a))
      else if query = D + b + 1 then state.getByte (BitVec.ofNat 64 (S + a + 1))
      else state.getByte (BitVec.ofNat 64 query) := by
  have loadAddress : state.getReg src + signExtend12 (BitVec.ofNat 12 a) = BitVec.ofNat 64 (S + a) := by
    rw [source, half_offset a aBound, ← BitVec.ofNat_add]
  let loaded := (state.setReg .x6 ((state.getHalfword (BitVec.ofNat 64 (S + a))).zeroExtend 64)).setPC
    (state.pc + 4)
  have first : execInstrBr state (.LHU .x6 src (BitVec.ofNat 12 a)) = loaded := by
    simp only [execInstrBr, loadAddress, loaded]
  have storeAddress : loaded.getReg dst + signExtend12 (BitVec.ofNat 12 b) = BitVec.ofNat 64 (D + b) := by
    simp only [loaded, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dstNe), target, half_offset b bBound,
      ← BitVec.ofNat_add]
  have value : (loaded.getReg .x6).truncate 16 = state.getHalfword (BitVec.ofNat 64 (S + a)) := by
    simp only [loaded, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide)]
    simp [BitVec.truncate_eq_setWidth]
  have memory : ∀ address : Word, loaded.getByte address = state.getByte address := by
    intro address
    simp only [loaded, MachineState.getByte, MachineState.getMem_setPC, MachineState.getMem_setReg]
  simp only [halfStep, first]
  simp only [execInstrBr, storeAddress, value]
  rw [show ∀ (t : MachineState) (v : Word) (q : Word), (t.setPC v).getByte q = t.getByte q from
      fun t v q => by simp only [MachineState.getByte, MachineState.getMem_setPC]]
  rw [set_halfword_get_byte _ _ _ _ targetEven (by omega) queryBound]
  simp only [memory]
  rw [get_halfword_eq _ _ sourceEven, append_low, append_high]

/-- One copy pair preserves every aligned doubleword outside the 8-byte block it writes. -/
theorem half_step_mem (src dst : Reg) (state : MachineState) (a b D word : Nat)
    (dstNe : dst ≠ .x6) (target : state.getReg dst = BitVec.ofNat 64 D) (bBound : b < 2048)
    (targetBound : D + b + 2 ≤ 2^64) (aligned : word % 8 = 0) (wordBound : word < 2^64)
    (different : word / 8 ≠ (D + b) / 8) :
    (halfStep src dst state a b).getMem (BitVec.ofNat 64 word) = state.getMem (BitVec.ofNat 64 word) := by
  simp only [halfStep, execInstrBr, MachineState.getMem_setPC]
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dstNe), target,
    half_offset b bBound, ← BitVec.ofNat_add,
    set_halfword_get_mem _ _ _ _ aligned (by omega) wordBound different]
  simp only [MachineState.getMem_setPC, MachineState.getMem_setReg]

/-- Exact byte effect of a copy run whose source and destination ranges are disjoint. -/
theorem half_run_byte (src dst : Reg) (state : MachineState) (a b S D k query : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : state.getReg src = BitVec.ofNat 64 S) (target : state.getReg dst = BitVec.ofNat 64 D)
    (aBound : a + 2 * k ≤ 2048) (bBound : b + 2 * k ≤ 2048)
    (sourceEven : (S + a) % 2 = 0) (targetEven : (D + b) % 2 = 0)
    (sourceBound : S + a + 2 * k ≤ 2^64) (targetBound : D + b + 2 * k ≤ 2^64)
    (separate : S + a + 2 * k ≤ D + b ∨ D + b + 2 * k ≤ S + a) (queryBound : query < 2^64) :
    (halfRun src dst state a b k).getByte (BitVec.ofNat 64 query) =
      if D + b ≤ query ∧ query < D + b + 2 * k then
        state.getByte (BitVec.ofNat 64 (S + a + (query - (D + b))))
      else state.getByte (BitVec.ofNat 64 query) := by
  induction k generalizing query with
  | zero => simp [halfRun]
  | succ k ih =>
    have ih' := fun q (qb : q < 2^64) => ih (aBound := by omega) (bBound := by omega)
      (sourceBound := by omega) (targetBound := by omega) (separate := by omega) (query := q)
      (queryBound := qb)
    rw [halfRun, half_step_byte src dst _ (a + 2 * k) (b + 2 * k) S D query srcNe dstNe
      ((half_run_register _ _ _ _ _ _ _ srcNe).trans source)
      ((half_run_register _ _ _ _ _ _ _ dstNe).trans target)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) queryBound]
    by_cases low : query = D + (b + 2 * k)
    · rw [if_pos low, if_pos (by omega), ← Nat.add_assoc, ih' _ (by omega), if_neg (by omega)]
      congr 2
      omega
    · rw [if_neg low]
      by_cases high : query = D + (b + 2 * k) + 1
      · rw [if_pos high, if_pos (by omega), ← Nat.add_assoc, ih' _ (by omega), if_neg (by omega)]
        congr 2
        omega
      · rw [if_neg high, ih' _ queryBound]
        by_cases inside : D + b ≤ query ∧ query < D + b + 2 * k
        · rw [if_pos inside, if_pos (by omega)]
        · rw [if_neg inside, if_neg (by omega)]

/-- A copy run preserves every aligned doubleword below its destination's first block or
at or after its end. -/
theorem half_run_mem (src dst : Reg) (state : MachineState) (a b D k word : Nat)
    (dstNe : dst ≠ .x6) (target : state.getReg dst = BitVec.ofNat 64 D)
    (bBound : b + 2 * k ≤ 2048) (targetBound : D + b + 2 * k ≤ 2^64)
    (aligned : word % 8 = 0) (wordBound : word < 2^64)
    (outside : word + 8 ≤ D + b ∨ D + b + 2 * k ≤ word) :
    (halfRun src dst state a b k).getMem (BitVec.ofNat 64 word) = state.getMem (BitVec.ofNat 64 word) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [halfRun, half_step_mem src dst _ (a + 2 * k) (b + 2 * k) D word dstNe
      ((half_run_register _ _ _ _ _ _ _ dstNe).trans target) (by omega) (by omega) aligned wordBound
      (by omega), ih (bBound := by omega) (targetBound := by omega) (outside := by omega)]

/-- The run's destination bytes are the source bytes (as a buffer read). -/
theorem half_run_copy (src dst : Reg) (state : MachineState) (a b S D k : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : state.getReg src = BitVec.ofNat 64 S) (target : state.getReg dst = BitVec.ofNat 64 D)
    (aBound : a + 2 * k ≤ 2048) (bBound : b + 2 * k ≤ 2048)
    (sourceEven : (S + a) % 2 = 0) (targetEven : (D + b) % 2 = 0)
    (sourceBound : S + a + 2 * k ≤ 2^64) (targetBound : D + b + 2 * k ≤ 2^64)
    (separate : S + a + 2 * k ≤ D + b ∨ D + b + 2 * k ≤ S + a) :
    readBuffer (halfRun src dst state a b k) (D + b) (2 * k) = readBuffer state (S + a) (2 * k) := by
  apply read_buffer_bytes_congr
  intro i inside
  rw [half_run_byte src dst state a b S D k _ srcNe dstNe source target aBound bBound sourceEven
    targetEven sourceBound targetBound separate (by omega), if_pos (by omega)]
  congr 2
  omega

/-- The run leaves every byte range disjoint from its destination unchanged. -/
theorem half_run_preserves (src dst : Reg) (state : MachineState) (a b S D k address count : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : state.getReg src = BitVec.ofNat 64 S) (target : state.getReg dst = BitVec.ofNat 64 D)
    (aBound : a + 2 * k ≤ 2048) (bBound : b + 2 * k ≤ 2048)
    (sourceEven : (S + a) % 2 = 0) (targetEven : (D + b) % 2 = 0)
    (sourceBound : S + a + 2 * k ≤ 2^64) (targetBound : D + b + 2 * k ≤ 2^64)
    (separate : S + a + 2 * k ≤ D + b ∨ D + b + 2 * k ≤ S + a)
    (readBound : address + count ≤ 2^64)
    (outside : address + count ≤ D + b ∨ D + b + 2 * k ≤ address) :
    readBuffer (halfRun src dst state a b k) address count = readBuffer state address count := by
  apply read_buffer_bytes_congr
  intro i inside
  rw [half_run_byte src dst state a b S D k _ srcNe dstNe source target aBound bBound sourceEven
    targetEven sourceBound targetBound separate (by omega), if_neg (by omega)]

/-- One copy pair changes no byte outside its two destination bytes (source arbitrary). -/
theorem half_step_byte_outside (src dst : Reg) (state : MachineState) (a b D query : Nat)
    (dstNe : dst ≠ .x6) (target : state.getReg dst = BitVec.ofNat 64 D) (bBound : b < 2048)
    (targetEven : (D + b) % 2 = 0) (targetBound : D + b + 2 ≤ 2^64) (queryBound : query < 2^64)
    (outside : query ≠ D + b ∧ query ≠ D + b + 1) :
    (halfStep src dst state a b).getByte (BitVec.ofNat 64 query) = state.getByte (BitVec.ofNat 64 query) := by
  have keep : ∀ (t : MachineState) (v : Word) (q : Word), (t.setPC v).getByte q = t.getByte q :=
    fun t v q => by simp only [MachineState.getByte, MachineState.getMem_setPC]
  have keepReg : ∀ (t : MachineState) (r : Reg) (v : Word) (q : Word), (t.setReg r v).getByte q = t.getByte q :=
    fun t r v q => by simp only [MachineState.getByte, MachineState.getMem_setReg]
  simp only [halfStep, execInstrBr, keep]
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dstNe), target,
    half_offset b bBound, ← BitVec.ofNat_add,
    set_halfword_get_byte _ _ _ _ targetEven (by omega) queryBound, if_neg outside.1, if_neg outside.2,
    keep, keepReg]

/-- A copy run changes no byte outside its destination range (source arbitrary). -/
theorem half_run_byte_outside (src dst : Reg) (state : MachineState) (a b D k query : Nat)
    (dstNe : dst ≠ .x6) (target : state.getReg dst = BitVec.ofNat 64 D) (bBound : b + 2 * k ≤ 2048)
    (targetEven : (D + b) % 2 = 0) (targetBound : D + b + 2 * k ≤ 2^64) (queryBound : query < 2^64)
    (outside : query < D + b ∨ D + b + 2 * k ≤ query) :
    (halfRun src dst state a b k).getByte (BitVec.ofNat 64 query) = state.getByte (BitVec.ofNat 64 query) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [halfRun, half_step_byte_outside src dst _ (a + 2 * k) (b + 2 * k) D query dstNe
      ((half_run_register _ _ _ _ _ _ _ dstNe).trans target) (by omega) (by omega) (by omega)
      queryBound (by omega), ih (bBound := by omega) (targetBound := by omega) (outside := by omega)]

/-- An aligned doubleword is determined by its eight bytes. -/
theorem get_mem_of_bytes (left right : MachineState) (word : Nat) (aligned : word % 8 = 0)
    (bytes : ∀ i < 8, left.getByte (BitVec.ofNat 64 (word + i)) = right.getByte (BitVec.ofNat 64 (word + i))) :
    left.getMem (BitVec.ofNat 64 word) = right.getMem (BitVec.ofNat 64 word) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j inside
  have equal := bytes (j / 8) (by omega)
  rw [nat_get_byte, nat_get_byte, show 8 * ((word + j / 8) / 8) = word by omega,
    show (word + j / 8) % 8 = j / 8 by omega] at equal
  have bit := congrArg (fun byte : BitVec 8 => byte.getLsbD (j % 8)) equal
  rw [extract_byte_getLsbD _ _ _ (by omega), extract_byte_getLsbD _ _ _ (by omega),
    show j / 8 * 8 + j % 8 = j by omega] at bit
  exact bit

/-- Halfword accesses inside memory at even addresses are valid. -/
theorem half_access_valid (base offset : Nat) (even : (base + offset) % 2 = 0)
    (bounded : base + offset + 2 ≤ MEMORY_BYTES) (offsetBound : offset < 2048) :
    accessValid (BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 offset)) 2 = true := by
  rw [half_offset offset offsetBound, ← BitVec.ofNat_add]
  have small : base + offset < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
  simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small]
  exact ⟨bounded, even⟩

/-- Exact interpreter execution of a copy run: `2k` unit-cost cycles and no queries,
provided the image holds the expected instructions and every access is valid. -/
theorem half_run_execute (image : Image) (src dst : Reg) (state : MachineState) (a b S D k : Nat)
    (srcNe : src ≠ .x6) (dstNe : dst ≠ .x6)
    (source : state.getReg src = BitVec.ofNat 64 S) (target : state.getReg dst = BitVec.ofNat 64 D)
    (aBound : a + 2 * k ≤ 2048) (bBound : b + 2 * k ≤ 2048)
    (sourceEven : (S + a) % 2 = 0) (targetEven : (D + b) % 2 = 0)
    (sourceBound : S + a + 2 * k ≤ MEMORY_BYTES) (targetBound : D + b + 2 * k ≤ MEMORY_BYTES)
    (loads : ∀ j < k, ∀ t : MachineState, t.pc = state.pc + BitVec.ofNat 64 (8 * j) →
      fetch image t = some (.base (.LHU .x6 src (BitVec.ofNat 12 (a + 2 * j)))))
    (stores : ∀ j < k, ∀ t : MachineState, t.pc = state.pc + BitVec.ofNat 64 (8 * j + 4) →
      fetch image t = some (.base (.SH dst .x6 (BitVec.ofNat 12 (b + 2 * j)))))
    (fuel : Nat) (allowCoins : Bool) :
    execute image (2 * k + fuel) state allowCoins =
      (do let result ← execute image fuel (halfRun src dst state a b k) allowCoins
          return result.charge (2 * k) 0) := by
  induction k generalizing fuel with
  | zero => simp [halfRun, Execution.charge]
  | succ k ih =>
    have ih' := ih (aBound := by omega) (bBound := by omega) (sourceBound := by omega)
      (targetBound := by omega) (loads := fun j hj => loads j (by omega))
      (stores := fun j hj => stores j (by omega))
    let current := halfRun src dst state a b k
    have currentSource : current.getReg src = BitVec.ofNat 64 S :=
      (half_run_register _ _ _ _ _ _ _ srcNe).trans source
    have currentTarget : current.getReg dst = BitVec.ofNat 64 D :=
      (half_run_register _ _ _ _ _ _ _ dstNe).trans target
    have currentPC : current.pc = state.pc + BitVec.ofNat 64 (8 * k) := half_run_pc _ _ _ _ _ _
    let loaded := execInstrBr current (.LHU .x6 src (BitVec.ofNat 12 (a + 2 * k)))
    have loadedPC : loaded.pc = state.pc + BitVec.ofNat 64 (8 * k + 4) := by
      change current.pc + 4 = _
      rw [currentPC, BitVec.add_assoc, BitVec.ofNat_add]
      rfl
    have loadedTarget : loaded.getReg dst = BitVec.ofNat 64 D := by
      simp only [loaded, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm dstNe), currentTarget]
    have loadStep : ordinaryStep current (.base (.LHU .x6 src (BitVec.ofNat 12 (a + 2 * k)))) =
        some loaded := by
      have valid := half_access_valid S (a + 2 * k) (by omega) (by omega) (by omega)
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, currentSource, valid, ↓reduceIte]
      rfl
    have storeStep : ordinaryStep loaded (.base (.SH dst .x6 (BitVec.ofNat 12 (b + 2 * k)))) =
        some (halfStep src dst current (a + 2 * k) (b + 2 * k)) := by
      have valid := half_access_valid D (b + 2 * k) (by omega) (by omega) (by omega)
      simp only [ordinaryStep, memoryArgumentsValid, memAccess, loadedTarget, valid, ↓reduceIte]
      rfl
    rw [show 2 * (k + 1) + fuel = 2 * k + (fuel + 1 + 1) by omega, ih' (fuel + 1 + 1),
      execute_ordinary_step _ _ _ _ _ _ (loads k (by omega) current currentPC) loadStep,
      execute_ordinary_step _ _ _ _ _ _ (stores k (by omega) loaded loadedPC) storeStep]
    simp only [bind_assoc, pure_bind, instructionCycles, Execution.charge]
    change (do
        let x ← execute image fuel (halfRun src dst state a b (k + 1)) allowCoins
        pure _) = _
    congr 1
    funext x
    congr 2
    · omega
    · omega

end CommitGolfCandidate.CKBHalf
