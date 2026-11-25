import CommitGolfCandidate.Check

/-! Byte/word refinement for the actual interpreter's little-endian memory.
These facts identify the compression syscall input with the stored digest words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem digits_nat (value count : Nat) :
    (∑ i ∈ Finset.range count, (value / 2^(8*i) % 256) * 2^(8*i)) = value % 2^(8*count) := by
  induction count with
  | zero => simp only [Finset.sum_range_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    simp only [Nat.reducePow, Nat.mul_comm]

private theorem digits_word (word : Word) :
    (∑ i ∈ Finset.range 8, (word.toNat / 2^(8*i) % 256) * 2^(8*i)) = word.toNat := by
  rw [digits_nat, Nat.mod_eq_of_lt word.isLt]

private theorem offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem address_decomposition (address : Word) :
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

/-- Address alignment and byte offsets, proved by arithmetic on the actual word
representation. Address wraparound does not affect the low three bits. -/
theorem aligned_byte (state : MachineState) (base i : Nat) (_bounded : i < 64) :
    state.getByte (BitVec.ofNat 64 (8 * base + i)) =
      extractByte (state.getMem (BitVec.ofNat 64 (8 * base + 8 * (i / 8)))) (i % 8) := by
  have offset : byteOffset (BitVec.ofNat 64 (8*base+i)) = i % 8 := by
    rw [offset_mod, BitVec.toNat_ofNat]
    omega
  have aligned : alignToDword (BitVec.ofNat 64 (8*base+i)) =
      BitVec.ofNat 64 (8*base+8*(i/8)) := by
    have parts := address_decomposition (BitVec.ofNat 64 (8*base+i))
    rw [offset] at parts
    have joined : BitVec.ofNat 64 (8*base+8*(i/8)) + BitVec.ofNat 64 (i%8) =
        BitVec.ofNat 64 (8*base+i) := by
      rw [← BitVec.ofNat_add]
      congr 1
      omega
    have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 (i%8)) (parts.trans joined.symm)
    simpa only [BitVec.add_sub_cancel] using canceled
  simp only [MachineState.getByte, aligned, offset]

private theorem append_nat {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toNat = high.toNat * 2^lowWidth + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

private def readNatural (state : MachineState) (address count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (state.getByte (BitVec.ofNat 64 (address+i))).toNat * 2^(8*i)

private theorem read_natural_add (state : MachineState) (address left right : Nat) :
    readNatural state address (left+right) = readNatural state address left +
      2^(8*left) * readNatural state (address+left) right := by
  unfold readNatural
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.mul_add, Nat.pow_add, Nat.add_assoc]
  ring

private theorem read_natural_bound (state : MachineState) (address count : Nat) :
    readNatural state address count < 2^(8*count) := by
  induction count with
  | zero => simp [readNatural]
  | succ count ih =>
    have byteBound := (state.getByte (BitVec.ofNat 64 (address+count))).isLt
    have termBound := Nat.mul_le_mul_right (2^(8*count))
      (show (state.getByte (BitVec.ofNat 64 (address+count))).toNat ≤ 255 by omega)
    rw [readNatural, Finset.sum_range_succ]
    change readNatural state address count + _ < _
    rw [Nat.mul_succ, Nat.pow_add]
    norm_num only [Nat.reducePow]
    omega

private theorem read_natural_word (state : MachineState) (address : Nat) (aligned : address % 8 = 0) :
    readNatural state address 8 = (state.getMem (BitVec.ofNat 64 address)).toNat := by
  obtain ⟨base, rfl⟩ : ∃ base, address = 8*base := ⟨address/8, by omega⟩
  unfold readNatural
  calc
    _ = ∑ i ∈ Finset.range 8,
        ((state.getMem (BitVec.ofNat 64 (8*base))).toNat / 2^(8*i) % 256) * 2^(8*i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have small := Finset.mem_range.mp hi
      rw [aligned_byte state base i (by omega)]
      simp only [Nat.div_eq_of_lt small, Nat.mod_eq_of_lt small,
        extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.mul_comm, Nat.zero_mul, Nat.add_zero]
    _ = _ := digits_word _

/-- A 32-byte read concatenates four consecutive words, low word first in memory. -/
theorem read_digest_words (state : MachineState) (address : Nat) (aligned : address % 8 = 0) :
    readBuffer state address 32 =
      ((state.getMem (BitVec.ofNat 64 (address + 24)) ++
        state.getMem (BitVec.ofNat 64 (address + 16))) ++
        state.getMem (BitVec.ofNat 64 (address + 8))) ++
        state.getMem (BitVec.ofNat 64 address) := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 256 (readNatural state address 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read_natural_bound state address 32)]
  rw [read_natural_add state address 24 8, read_natural_add state address 16 8,
    read_natural_add state address 8 8]
  rw [read_natural_word state address aligned,
    read_natural_word state (address+8) (by omega),
    read_natural_word state (address+16) (by omega),
    read_natural_word state (address+24) (by omega)]
  simp only [append_nat]
  norm_num
  ring

set_option exponentiation.threshold 512 in
/-- A compression input consists of its upper 32-byte block and lower digest. -/
theorem read_compression_halves (state : MachineState) (address : Nat)
    (_aligned : address % 8 = 0) :
    readBuffer state address 64 =
      readBuffer state (address + 32) 32 ++ readBuffer state address 32 := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 512 (readNatural state address 64)).toNat =
    ((BitVec.ofNat 256 (readNatural state (address+32) 32)) ++
      (BitVec.ofNat 256 (readNatural state address 32))).toNat
  rw [append_nat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (read_natural_bound state address 64),
    Nat.mod_eq_of_lt (read_natural_bound state (address+32) 32),
    Nat.mod_eq_of_lt (read_natural_bound state address 32), read_natural_add state address 32 32]
  ring

/-- Reads depend only on the words in the addressed digest. -/
theorem read_digest_congr (left right : MachineState) (address : Nat)
    (aligned : address % 8 = 0)
    (words : ∀ i < 4, left.getMem (BitVec.ofNat 64 (address + 8*i)) =
      right.getMem (BitVec.ofNat 64 (address + 8*i))) :
    readBuffer left address 32 = readBuffer right address 32 := by
  rw [read_digest_words _ _ aligned, read_digest_words _ _ aligned]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]

/-- Extracting one word of the loaded digest recovers the corresponding memory word. -/
theorem read_digest_word (state : MachineState) (address word : Nat)
    (aligned : address % 8 = 0) (bounded : word < 4) :
    (readBuffer state address 32).extractLsb' (64*word) 64 =
      state.getMem (BitVec.ofNat 64 (address+8*word)) := by
  rw [read_digest_words _ _ aligned]
  interval_cases word
  · exact BitVec.extractLsb'_append_eq_right
  · exact (BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)).trans
      BitVec.extractLsb'_append_eq_right
  · exact (BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)).trans
      ((BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)).trans
        BitVec.extractLsb'_append_eq_right)
  · exact (BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 192)).trans
      ((BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)).trans
        BitVec.extractLsb'_append_eq_left)

/-- Digest equality is exactly the four word comparisons performed by the checker. -/
theorem read_digest_eq_iff (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0) :
    readBuffer left leftAddress 32 = readBuffer right rightAddress 32 ↔
      ∀ word < 4, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
        right.getMem (BitVec.ofNat 64 (rightAddress+8*word)) := by
  constructor
  · intro equal word bounded
    have extracted := congrArg (fun digest : BitVec 256 => digest.extractLsb' (64*word) 64) equal
    simpa only [read_digest_word _ _ _ leftAligned bounded,
      read_digest_word _ _ _ rightAligned bounded] using extracted
  · intro words
    rw [read_digest_words _ _ leftAligned, read_digest_words _ _ rightAligned]
    have w0 := words 0 (by decide)
    have w1 := words 1 (by decide)
    have w2 := words 2 (by decide)
    have w3 := words 3 (by decide)
    simp only [Nat.reduceMul, Nat.add_zero] at w0 w1 w2 w3
    rw [w0, w1, w2, w3]

/-- The compression reply is read back as the identical 256-bit digest. -/
theorem check_leaf_ecall_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkLeafEcallState state answer) 256 32 = answer := by
  rw [read_digest_words _ _ (by decide)]
  have w0 := check_leaf_ecall_word state answer 0 (by decide)
  have w1 := check_leaf_ecall_word state answer 1 (by decide)
  have w2 := check_leaf_ecall_word state answer 2 (by decide)
  have w3 := check_leaf_ecall_word state answer 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

theorem check_compression_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkCompressionState state answer) 256 32 = answer := by
  rw [read_digest_words _ _ (by decide)]
  have w0 := check_compression_word state answer 0 (by decide)
  have w1 := check_compression_word state answer 1 (by decide)
  have w2 := check_compression_word state answer 2 (by decide)
  have w3 := check_compression_word state answer 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

end CommitGolfCandidate
