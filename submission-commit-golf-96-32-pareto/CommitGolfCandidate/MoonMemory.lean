import CommitGolfCandidate.MoonImage
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.WriteMemoryCore

/-! Byte- and doubleword-exact memory lemmas for the pure 3-ary FIFO queue machine images:
- Aligned `setMem` / `readBuffer` semantics
- 96-byte compression buffer decompositions (`leafA`, `lateEven`, `lateOdd`, 3-ary)
- ABI initial buffer contents for commit, opening, and check under our exact layout
- `DIVU` by 3 and sorted-value index correspondence. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-! ### Byte and Dword Memory Semantics -/

private theorem byteOffset_lt (a : Word) : byteOffset a < 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem byteOffset_eq_mod (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change a.toNat &&& (2 ^ 3 - 1) = a.toNat % 2 ^ 3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem alignToDword_add_byteOffset (a : Word) :
    alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disj : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases (7#64)[i] <;> simp
  have comb : (a &&& ~~~7#64) ||| (a &&& 7#64) = a := by
    ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disj, comb]

theorem alignToDword_ofNat_eq (base off : Nat) (hoff : off < 8) (hbase : base % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (base + off)) = BitVec.ofNat 64 base := by
  have hbo : byteOffset (BitVec.ofNat 64 (base + off)) = off := by
    rw [byteOffset_eq_mod, BitVec.toNat_ofNat]
    omega
  have hp := alignToDword_add_byteOffset (BitVec.ofNat 64 (base + off))
  rw [hbo] at hp
  have hj : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) :=
    (BitVec.ofNat_add _ _).symm
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 off) (hp.trans hj.symm)
  simpa only [BitVec.add_sub_cancel] using hc

/-- `setMem` at an 8-byte aligned address updates only bytes in `[addr, addr + 8)`. -/
theorem setMem_getByte_outside (state : MachineState) (addr query val : Word)
    (halign : addr.toNat % 8 = 0)
    (hsep : alignToDword query ≠ addr) :
    (state.setMem addr val).getByte query = state.getByte query := by
  simp only [MachineState.getByte, MachineState.getMem_setMem_ne hsep]

theorem setMem_getByte_ofNat (state : MachineState) (addr q : Nat) (val : Word)
    (halign : addr % 8 = 0) (ha : addr + 8 ≤ 2 ^ 64) (hq : q < 2 ^ 64)
    (hout : q < addr ∨ addr + 8 ≤ q) :
    (state.setMem (BitVec.ofNat 64 addr) val).getByte (BitVec.ofNat 64 q) =
      state.getByte (BitVec.ofNat 64 q) := by
  have hal : (BitVec.ofNat 64 addr).toNat % 8 = 0 := by
    have hlt : addr < 2 ^ 64 := by omega
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; exact halign
  apply setMem_getByte_outside state _ _ val hal
  intro heq
  have hdec := alignToDword_ofNat_eq (8 * (q / 8)) (q % 8) (by omega) (by omega)
  have hqeq : 8 * (q / 8) + q % 8 = q := by omega
  rw [hqeq] at hdec
  rw [hdec] at heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (q / 8) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : addr < 2 ^ 64)] at hn
  omega

theorem setMem_getByte_inside (state : MachineState) (addr j : Nat) (val : Word)
    (halign : addr % 8 = 0) (hj : j < 8) :
    (state.setMem (BitVec.ofNat 64 addr) val).getByte (BitVec.ofNat 64 (addr + j)) =
      val.extractLsb' (8 * j) 8 := by
  have hal := alignToDword_ofNat_eq addr j hj halign
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    rw [byteOffset_eq_mod, BitVec.toNat_ofNat]; omega
  simp only [MachineState.getByte, hal, hbo, MachineState.getMem_setMem_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mul_comm 8 j]

/-! ### `readBuffer` Congruences and 96-Byte Splits -/

theorem readBuffer_congr (s1 s2 : MachineState) (addr n : Nat)
    (h : ∀ j < n, s1.getByte (BitVec.ofNat 64 (addr + j)) = s2.getByte (BitVec.ofNat 64 (addr + j))) :
    readBuffer s1 addr n = readBuffer s2 addr n := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem readBuffer_zero_of_bytes (s : MachineState) (addr n : Nat)
    (h : ∀ j < n, s.getByte (BitVec.ofNat 64 (addr + j)) = 0) :
    readBuffer s addr n = 0 := by
  unfold readBuffer
  have hsum : ∑ j ∈ Finset.range n, (s.getByte (BitVec.ofNat 64 (addr + j))).toNat * 2 ^ (8 * j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj)]
    simp
  rw [hsum]; rfl

theorem readBuffer_word (s : MachineState) (addr : Nat) (halign : addr % 8 = 0) :
    readBuffer s addr 8 = s.getMem (BitVec.ofNat 64 addr) := by
  have sl := read_buffer_slice s addr 32 0 8 (by decide)
  have wd := read_digest_word s addr 0 halign (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero] using sl.symm.trans wd

private theorem bv_append_toNat {hi lo : Nat} (a : BitVec hi) (b : BitVec lo) :
    (a ++ b).toNat = a.toNat * 2 ^ lo + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

private theorem sum_range_bytes_lt (s : MachineState) (addr n : Nat) :
    (∑ i ∈ Finset.range n, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) < 2 ^ (8 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := (s.getByte (BitVec.ofNat 64 (addr + n))).isLt
    have ht := Nat.mul_le_mul_right (2 ^ (8 * n)) (show (s.getByte (BitVec.ofNat 64 (addr + n))).toNat ≤ 255 by omega)
    rw [Finset.sum_range_succ, Nat.mul_succ, Nat.pow_add]
    norm_num only [Nat.reducePow]
    omega

private theorem sum_range_bytes_add (s : MachineState) (addr a b : Nat) :
    (∑ i ∈ Finset.range (a + b), (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) =
      (∑ i ∈ Finset.range a, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) +
      2 ^ (8 * a) * (∑ i ∈ Finset.range b, (s.getByte (BitVec.ofNat 64 (addr + a + i))).toNat * 2 ^ (8 * i)) := by
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.mul_add, Nat.pow_add, Nat.add_assoc]
  ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_leafA (s : MachineState) (addr : Nat) :
    readBuffer s addr 96 =
      readBuffer s (addr + 32) 64 ++ readBuffer s addr 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 32 64
  rw [show (96 : Nat) = 32 + 64 from rfl, h1]
  norm_num; ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_lateEven (s : MachineState) (addr : Nat)
    (hgap : readBuffer s (addr + 64) 8 = 0) :
    readBuffer s addr 96 =
      leafFinalEven (readBuffer s addr 32) (readBuffer s (addr + 32) 32) (readBuffer s (addr + 72) 24) := by
  unfold leafFinalEven
  apply BitVec.eq_of_toNat_eq
  have hgapNat : (∑ i ∈ Finset.range 8, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i)) = 0 := by
    have ht := congrArg BitVec.toNat hgap
    change (BitVec.ofNat (8 * 8) _).toNat = 0 at ht
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)] using ht
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 32 64
  have h2 := sum_range_bytes_add s (addr + 32) 32 32
  have h3 := sum_range_bytes_add s (addr + 64) 8 24
  have ha1 : addr + 32 + 32 = addr + 64 := by omega
  have ha2 : addr + 64 + 8 = addr + 72 := by omega
  rw [ha1] at h2
  rw [ha2] at h3
  have h1' : (∑ i ∈ Finset.range 96, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) = _ := h1
  have h2' : (∑ i ∈ Finset.range 64, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) = _ := h2
  have h3' : (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i)) = _ := h3
  rw [h1', h2', h3', hgapNat]
  norm_num; ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_lateOdd (s : MachineState) (addr : Nat)
    (hgap : readBuffer s (addr + 24) 8 = 0) :
    readBuffer s addr 96 =
      leafFinalOdd (readBuffer s (addr + 32) 32) (readBuffer s (addr + 64) 32) (readBuffer s addr 24) := by
  unfold leafFinalOdd
  apply BitVec.eq_of_toNat_eq
  have hgapNat : (∑ i ∈ Finset.range 8, (s.getByte (BitVec.ofNat 64 (addr + 24 + i))).toNat * 2 ^ (8 * i)) = 0 := by
    have ht := congrArg BitVec.toNat hgap
    change (BitVec.ofNat (8 * 8) _).toNat = 0 at ht
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)] using ht
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 24 72
  have h2 := sum_range_bytes_add s (addr + 24) 8 64
  have h3 := sum_range_bytes_add s (addr + 32) 32 32
  have ha1 : addr + 24 + 8 = addr + 32 := by omega
  have ha2 : addr + 32 + 32 = addr + 64 := by omega
  rw [ha1] at h2
  rw [ha2] at h3
  have h1' : (∑ i ∈ Finset.range 96, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) = _ := h1
  have h2' : (∑ i ∈ Finset.range 72, (s.getByte (BitVec.ofNat 64 (addr + 24 + i))).toNat * 2 ^ (8 * i)) = _ := h2
  have h3' : (∑ i ∈ Finset.range 64, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) = _ := h3
  rw [h1', h2', h3', hgapNat]
  norm_num; ring

set_option exponentiation.threshold 1024 in
theorem readBuffer_ternary (s : MachineState) (addr : Nat) :
    readBuffer s addr 96 =
      ternaryInput (readBuffer s addr 32) (readBuffer s (addr + 32) 32) (readBuffer s (addr + 64) 32) := by
  unfold ternaryInput
  apply BitVec.eq_of_toNat_eq
  simp only [readBuffer, bv_append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (sum_range_bytes_lt s _ _)]
  have h1 := sum_range_bytes_add s addr 32 64
  have h2 := sum_range_bytes_add s (addr + 32) 32 32
  have h64 : addr + 32 + 32 = addr + 64 := by omega
  rw [h64] at h2
  have h96 : (∑ i ∈ Finset.range 96, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) =
      (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + i))).toNat * 2 ^ (8 * i)) +
      2 ^ 256 * ((∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) +
      2 ^ 256 * (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i))) := by
    change (∑ i ∈ Finset.range (32 + 64), _) = _
    rw [h1]
    have h2' : (∑ i ∈ Finset.range (32 + 32), (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) =
        (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) +
        2 ^ (8 * 32) * (∑ i ∈ Finset.range 32, (s.getByte (BitVec.ofNat 64 (addr + 64 + i))).toNat * 2 ^ (8 * i)) := h2
    rw [show (∑ i ∈ Finset.range 64, (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) =
        (∑ i ∈ Finset.range (32 + 32), (s.getByte (BitVec.ofNat 64 (addr + 32 + i))).toNat * 2 ^ (8 * i)) from rfl, h2']
  rw [h96]; norm_num; ring

theorem writeBits_readBuffer_slice {bits : Nat} (state : MachineState) (address offset count : Nat)
    (answer : BitVec bits) (inside : offset + count ≤ (bits + 7) / 8)
    (bounded : (bits + 7) / 8 ≤ 2 ^ 64) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) (address + offset) count =
      answer.extractLsb' (8 * offset) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  have w := write_bits_byte state (BitVec.ofNat 64 address) answer (offset + j) (by omega) bounded
  simpa only [BitVec.ofNat_add, Nat.add_assoc, BitVec.add_assoc] using w

theorem writeBits_readBuffer_digest (state : MachineState) (address : Nat) (answer : Digest) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) address 32 = answer := by
  have h := writeBits_readBuffer_slice state address 0 32 answer (by decide) (by decide)
  simpa using h

theorem writeBits_readBuffer_pairSaltEven (state : MachineState) (address : Nat) (r : PairRand) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) r) address 24 = pairSaltEven r := by
  have h := writeBits_readBuffer_slice state address 0 24 r (by decide) (by decide)
  simpa [pairSaltEven] using h

theorem writeBits_readBuffer_pairSaltOdd (state : MachineState) (address : Nat) (r : PairRand) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) r) (address + 16) 24 = pairSaltOdd r := by
  have h := writeBits_readBuffer_slice state address 16 24 r (by decide) (by decide)
  simpa [pairSaltOdd] using h

/-! ### `DIVU` by 3 -/

theorem rv64_divu_three (x : Word) :
    rv64_divu x 3#64 = BitVec.ofNat 64 (x.toNat / 3) := by
  unfold rv64_divu
  have hne : (3#64 == 0#64) = false := by decide
  rw [hne]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv, BitVec.toNat_ofNat]
  have hlt : x.toNat / 3 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  rw [Nat.mod_eq_of_lt hlt]
  rfl

/-! ### Sorted Position / Value Correspondence -/

def openingIndex (positions : Positions) (ordinal : Nat) : Nat :=
  if h : ordinal < positions.card then
    ((positions.sort (· ≤ ·))[ordinal]'(by simpa using h)).val
  else 0

theorem openingIndex_lt (positions : Positions) (ordinal : Nat) :
    openingIndex positions ordinal < LENGTH := by
  unfold openingIndex
  split
  · exact ((positions.sort (· ≤ ·))[ordinal]'(by simpa)).isLt
  · unfold LENGTH LOG_LENGTH; omega

theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

theorem sorted_value_index (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    (((positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val).val =
      openingIndex positions ordinal := by
  have attachedBound : ordinal < (positions.attach.sort (fun i j => i.val ≤ j.val)).length := by
    simpa using present
  have positionBound : ordinal < (positions.sort (· ≤ ·)).length := by simpa using present
  have same := congrArg (fun list : List Index => list[ordinal]?) (sorted_value_indices positions)
  simp only [List.getElem?_map, List.getElem?_eq_getElem attachedBound,
    List.getElem?_eq_getElem positionBound, Option.map_some, Option.some.injEq] at same
  rw [same]
  simp only [openingIndex, dif_pos present]

/-! ### ABI Initial State Contents for Our Exact Layout -/

private theorem positions_card_le_length (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

theorem commit_initial_msg_byte (message : Message) (index : Index) (offset : Nat)
    (inside : offset < 256) :
    (submission.initialState .commit message).getByte
      (BitVec.ofNat 64 (4096 + 256 * index.val + offset)) =
        (message index).extractLsb' (8 * offset) 8 := by
  have hi : index.val < 16777216 := index.isLt
  rw [initial_input_byte submission .commit message _ (by omega)]
  have hsel : submission.layout.message ≤ 4096 + 256 * index.val + offset ∧
      4096 + 256 * index.val + offset < submission.layout.message + LENGTH * (LEAF_SIZE / 8) := by
    change 4096 ≤ _ ∧ _ < 4096 + 16777216 * 256; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, hsel, and_self, decide_true]
  have hq : (4096 + 256 * index.val + offset - submission.layout.message) / (LEAF_SIZE / 8) = index.val := by
    change (4096 + 256 * index.val + offset - 4096) / 256 = _; omega
  have hr : (4096 + 256 * index.val + offset - submission.layout.message) % (LEAF_SIZE / 8) = offset := by
    change (4096 + 256 * index.val + offset - 4096) % 256 = _; omega
  simp only [hq, hr, index.isLt, dite_true]

theorem commit_initial_msg_slice (message : Message) (index : Index) (off count : Nat)
    (hbound : off + count ≤ 256) :
    readBuffer (submission.initialState .commit message) (4096 + 256 * index.val + off) count =
      (message index).extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using commit_initial_msg_byte message index (off + j) (by omega)

theorem commit_initial_zero_byte (message : Message) (addr : Nat)
    (hout : addr < 4096 ∨ (4096 + 2 ^ 32 ≤ addr ∧ addr < 68719476736)) :
    (submission.initialState .commit message).getByte (BitVec.ofNat 64 addr) = 0 := by
  rw [initial_input_byte submission .commit message _ (by omega)]
  have hnsel : ¬ (submission.layout.message ≤ addr ∧
      addr < submission.layout.message + LENGTH * (LEAF_SIZE / 8)) := by
    change ¬ (4096 ≤ addr ∧ addr < 4096 + 16777216 * 256); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer, hnsel,
    decide_false, List.find?_nil, commit_dataBase]
  rw [if_neg (by omega)]

theorem opening_initial_trapdoor_byte (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (off : Nat) (hoff : off < 2348810240) :
    (submission.initialState .opening (trapdoor, positions)).getByte
      (BitVec.ofNat 64 (4294971424 + off)) = trapdoor.extractLsb' (8 * off) 8 := by
  rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
  have hsel : submission.layout.trapdoor ≤ 4294971424 + off ∧
      4294971424 + off < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8 := by
    change 4294971424 ≤ _ ∧ _ < 4294971424 + (8 * 2348810240 + 7) / 8; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, hsel, and_self,
    decide_true, show 4294971424 + off - submission.layout.trapdoor = off by
      change 4294971424 + off - 4294971424 = off; omega]

theorem opening_initial_trapdoor_slice (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (off count : Nat) (hbound : off + count ≤ 2348810240) :
    readBuffer (submission.initialState .opening (trapdoor, positions)) (4294971424 + off) count =
      trapdoor.extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using opening_initial_trapdoor_byte trapdoor positions (off + j) (by omega)

theorem opening_initial_index (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (ordinal : Nat) (hord : ordinal < positions.card) :
    (submission.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (6643781664 + 8 * ordinal)) =
        BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le_length positions
  let idx := (positions.sort (· ≤ ·))[ordinal]'(by simpa using hord)
  have hidx : idx.val < 16777216 := idx.isLt
  have hbytes : ∀ j < 8,
      (submission.initialState .opening (trapdoor, positions)).getByte
        (BitVec.ofNat 64 (6643781664 + 8 * ordinal + j)) =
          (BitVec.ofNat 64 idx.val).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
    have hnot_td : ¬ (submission.layout.trapdoor ≤ 6643781664 + 8 * ordinal + j ∧
        6643781664 + 8 * ordinal + j < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
      change ¬ (4294971424 ≤ _ ∧ _ < 4294971424 + (8 * 2348810240 + 7) / 8); omega
    have hsel : submission.layout.indices ≤ 6643781664 + 8 * ordinal + j ∧
        6643781664 + 8 * ordinal + j < submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; change 6643781664 ≤ _ ∧ _ < 6643781664 + 8 * positions.card; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      hnot_td, decide_false, hsel, and_self, decide_true]
    have hq : (6643781664 + 8 * ordinal + j - submission.layout.indices) / 8 = ordinal := by
      change (6643781664 + 8 * ordinal + j - 6643781664) / 8 = _; omega
    have hr : (6643781664 + 8 * ordinal + j - submission.layout.indices) % 8 = j := by
      change (6643781664 + 8 * ordinal + j - 6643781664) % 8 = _; omega
    rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    rfl
  have hd := read_serialized_slice (submission.initialState .opening (trapdoor, positions))
    (BitVec.ofNat 64 idx.val) (6643781664 + 8 * ordinal) 0 8 (by simpa only [Nat.zero_add] using hbytes)
  rw [readBuffer_word _ _ (by omega)] at hd
  simpa only [Nat.mul_zero, Nat.mul_one, BitVec.extractLsb'_eq_self, openingIndex, dif_pos hord] using hd

theorem opening_initial_zero_low (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (addr : Nat) (haddr : addr < 4294971424) :
    (submission.initialState .opening (trapdoor, positions)).getByte (BitVec.ofNat 64 addr) = 0 := by
  have hcard := positions_card_le_length positions
  rw [initial_input_byte submission .opening (trapdoor, positions) _ (by omega)]
  have h1 : ¬ (submission.layout.trapdoor ≤ addr ∧
      addr < submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
    change ¬ (4294971424 ≤ addr ∧ _); omega
  have h2 : ¬ (submission.layout.indices ≤ addr ∧
      addr < submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length) := by
    change ¬ (6643781664 ≤ addr ∧ _); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    h1, h2, decide_false, List.find?_nil, opening_dataBase]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

theorem check_initial_commitment (input : CheckInput) :
    readBuffer (submission.initialState .check input) 4294971392 32 = input.commitment := by
  have hd := read_serialized_slice (submission.initialState .check input) input.commitment 4294971392 0 32 (by
    intro j hj
    rw [initial_input_byte submission .check input _ (by omega)]
    have hsel : submission.layout.commitment ≤ 4294971392 + j ∧
        4294971392 + j < submission.layout.commitment + (DIGEST_BITS + 7) / 8 := by
      change 4294971392 ≤ _ ∧ _ < 4294971392 + 32; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, hsel, and_self,
      decide_true, Nat.zero_add, show 4294971392 + j - submission.layout.commitment = j by
        change 4294971392 + j - 4294971392 = j; omega])
  exact hd.trans BitVec.extractLsb'_eq_self

theorem check_initial_index (input : CheckInput) (ordinal : Nat) (hord : ordinal < input.positions.card) :
    (submission.initialState .check input).getMem (BitVec.ofNat 64 (6643781664 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex input.positions ordinal) := by
  have hcard := positions_card_le_length input.positions
  let idx := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using hord)
  have hidx : idx.val < 16777216 := idx.isLt
  have hbytes : ∀ j < 8,
      (submission.initialState .check input).getByte (BitVec.ofNat 64 (6643781664 + 8 * ordinal + j)) =
        (BitVec.ofNat 64 idx.val).extractLsb' (8 * j) 8 := by
    intro j hj
    rw [initial_input_byte submission .check input _ (by omega)]
    have h1 : ¬ (submission.layout.commitment ≤ 6643781664 + 8 * ordinal + j ∧
        6643781664 + 8 * ordinal + j < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
      change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
    have hsel : submission.layout.indices ≤ 6643781664 + 8 * ordinal + j ∧
        6643781664 + 8 * ordinal + j < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; change 6643781664 ≤ _ ∧ _ < 6643781664 + 8 * input.positions.card; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      h1, decide_false, hsel, and_self, decide_true]
    have hq : (6643781664 + 8 * ordinal + j - submission.layout.indices) / 8 = ordinal := by
      change (6643781664 + 8 * ordinal + j - 6643781664) / 8 = _; omega
    have hr : (6643781664 + 8 * ordinal + j - submission.layout.indices) % 8 = j := by
      change (6643781664 + 8 * ordinal + j - 6643781664) % 8 = _; omega
    rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    rfl
  have hd := read_serialized_slice (submission.initialState .check input)
    (BitVec.ofNat 64 idx.val) (6643781664 + 8 * ordinal) 0 8 (by simpa only [Nat.zero_add] using hbytes)
  rw [readBuffer_word _ _ (by omega)] at hd
  simpa only [Nat.mul_zero, Nat.mul_one, BitVec.extractLsb'_eq_self, openingIndex, dif_pos hord] using hd

theorem check_initial_value_byte (input : CheckInput) (ordinal offset : Nat)
    (hord : ordinal < input.positions.card) (hoff : offset < 256) :
    (submission.initialState .check input).getByte
      (BitVec.ofNat 64 (6777999392 + 256 * ordinal + offset)) =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using hord))).extractLsb' (8 * offset) 8 := by
  have hcard := positions_card_le_length input.positions
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ 6777999392 + 256 * ordinal + offset ∧
      6777999392 + 256 * ordinal + offset < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
  have h2 : ¬ (submission.layout.indices ≤ 6777999392 + 256 * ordinal + offset ∧
      6777999392 + 256 * ordinal + offset < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (6643781664 ≤ _ ∧ _ < 6643781664 + 8 * input.positions.card); omega
  have hsel : submission.layout.values ≤ 6777999392 + 256 * ordinal + offset ∧
      6777999392 + 256 * ordinal + offset < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length := by
    rw [Finset.length_sort, Finset.card_attach]
    change 6777999392 ≤ _ ∧ _ < 6777999392 + 256 * input.positions.card; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, decide_false, hsel, and_self, decide_true]
  have hq : (6777999392 + 256 * ordinal + offset - submission.layout.values) / (LEAF_SIZE / 8) = ordinal := by
    change (6777999392 + 256 * ordinal + offset - 6777999392) / 256 = _; omega
  have hr : (6777999392 + 256 * ordinal + offset - submission.layout.values) % (LEAF_SIZE / 8) = offset := by
    change (6777999392 + 256 * ordinal + offset - 6777999392) % 256 = _; omega
  rw [hq, hr, List.getElem?_eq_getElem (by simpa using hord)]

theorem check_initial_value_slice (input : CheckInput) (ordinal off count : Nat)
    (hord : ordinal < input.positions.card) (hbound : off + count ≤ 256) :
    readBuffer (submission.initialState .check input) (6777999392 + 256 * ordinal + off) count =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using hord))).extractLsb' (8 * off) (8 * count) := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using check_initial_value_byte input ordinal (off + j) hord (by omega)

theorem check_initial_proof_byte (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof) (off : Nat)
    (hoff : off < input.proof.length) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 (11072966688 + off)) =
      input.proof[off] := by
  have hcard := positions_card_le_length input.positions
  change input.proof.length ≤ 11140077536 at hvalid
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ 11072966688 + off ∧
      11072966688 + off < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ _ ∧ _ < 4294971392 + 32); omega
  have h2 : ¬ (submission.layout.indices ≤ 11072966688 + off ∧
      11072966688 + off < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]; change ¬ (6643781664 ≤ _ ∧ _ < 6643781664 + 8 * input.positions.card); omega
  have h3 : ¬ (submission.layout.values ≤ 11072966688 + off ∧
      11072966688 + off < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    rw [Finset.length_sort, Finset.card_attach]
    change ¬ (6777999392 ≤ _ ∧ _ < 6777999392 + 256 * input.positions.card); omega
  have hsel : submission.layout.proof ≤ 11072966688 + off ∧
      11072966688 + off < submission.layout.proof + input.proof.length := by
    change 11072966688 ≤ _ ∧ _ < 11072966688 + input.proof.length; omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, h3, decide_false, hsel, and_self, decide_true,
    show 11072966688 + off - submission.layout.proof = off by
      change 11072966688 + off - 11072966688 = off; omega,
    List.getElem?_eq_getElem hoff, Option.getD_some]

theorem check_initial_zero_low (input : CheckInput) (addr : Nat) (haddr : addr < 4294971392) :
    (submission.initialState .check input).getByte (BitVec.ofNat 64 addr) = 0 := by
  have hcard := positions_card_le_length input.positions
  rw [initial_input_byte submission .check input _ (by omega)]
  have h1 : ¬ (submission.layout.commitment ≤ addr ∧
      addr < submission.layout.commitment + (DIGEST_BITS + 7) / 8) := by
    change ¬ (4294971392 ≤ addr ∧ _); omega
  have h2 : ¬ (submission.layout.indices ≤ addr ∧
      addr < submission.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    change ¬ (6643781664 ≤ addr ∧ _); omega
  have h3 : ¬ (submission.layout.values ≤ addr ∧
      addr < submission.layout.values + (LEAF_SIZE / 8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    change ¬ (6777999392 ≤ addr ∧ _); omega
  have h4 : ¬ (submission.layout.proof ≤ addr ∧ addr < submission.layout.proof + input.proof.length) := by
    change ¬ (11072966688 ≤ addr ∧ _); omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
    valuesBuffer, h1, h2, h3, h4, decide_false, List.find?_nil, check_dataBase]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-! ### Shared Contract: Honest Committed Trapdoor Contents -/

def CommittedTrapdoor (h768 : COMPRESSION_INPUT_LENGTH = 768) (c : Compression)
    (msg : Message) (salts : Index → Salt192)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) : Prop :=
  let c96 : Comp96 := fun x => c (x.cast h768.symm)
  (∀ v < TREE_NODES,
    trapdoor.extractLsb' (8 * (32 * v)) 256 = nodeVal c96 msg salts v) ∧
  (∀ i : Index,
    trapdoor.extractLsb' (8 * saltOff i) 192 = salts i)

end CommitGolfCandidate
