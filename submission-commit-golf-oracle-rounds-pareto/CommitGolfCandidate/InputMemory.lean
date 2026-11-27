import CommitGolfCandidate.Memory

/-! Exact byte contents of the trusted input loader. These lemmas connect serialized
messages, commitments, private state, and proofs to the machine's memory reads. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- The byte selected by the input ABI, including its zero/data fallback. -/
def inputByte (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address : Nat) : Byte :=
  match (candidate.inputBuffers program input).find?
      (fun buffer => decide (buffer.address ≤ address ∧ address < buffer.address + buffer.length)) with
  | some buffer => buffer.byteAt (address - buffer.address)
  | none => if dataBase (candidate.image program) ≤ address then
      (candidate.image program).data[address - dataBase (candidate.image program)]?.getD 0
    else 0

private theorem extract_packed_byte (bytes : Nat → Byte) (i : Nat) (hi : i < 8) :
    extractByte (BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (bytes j).toNat * 2^(8*j))) i = bytes i := by
  have bounds : ∀ j, (bytes j).toNat < 256 := fun j => (bytes j).isLt
  have b0 := bounds 0
  have b1 := bounds 1
  have b2 := bounds 2
  have b3 := bounds 3
  have b4 := bounds 4
  have b5 := bounds 5
  have b6 := bounds 6
  have b7 := bounds 7
  apply BitVec.eq_of_toNat_eq
  interval_cases i <;>
    norm_num [extractByte, BitVec.truncate, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Finset.sum_range_succ] <;> omega

/-- Register initialization does not change the word assembled from the input bytes. -/
theorem initial_input_word (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address : Nat) (bounded : address < 2^64) :
    (candidate.initialState program input).getMem (BitVec.ofNat 64 address) =
      BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
        (inputByte candidate program input (address+j)).toNat * 2^(8*j)) := by
  change BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (inputByte candidate program input ((BitVec.ofNat 64 address).toNat+j)).toNat * 2^(8*j)) = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]

/-- Every byte read from initialized memory is exactly the byte selected by the ABI. -/
theorem initial_input_byte (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address : Nat) (bounded : address < 2^64) :
    (candidate.initialState program input).getByte (BitVec.ofNat 64 address) =
      inputByte candidate program input address := by
  have decomposition : address = 8*(address/8) + address%8 := by omega
  calc
    _ = extractByte ((candidate.initialState program input).getMem
        (BitVec.ofNat 64 (8*(address/8)))) (address%8) := by
      conv_lhs => rw [decomposition]
      simpa only [Nat.div_eq_of_lt (show address%8 < 8 by omega), Nat.mul_zero,
        Nat.add_zero, Nat.mod_eq_of_lt (show address%8 < 8 by omega)] using
        aligned_byte (candidate.initialState program input) (address/8) (address%8) (by omega)
    _ = inputByte candidate program input (8*(address/8)+address%8) := by
      rw [initial_input_word candidate program input _ (by omega)]
      exact extract_packed_byte _ _ (by omega)
    _ = _ := congrArg (inputByte candidate program input) decomposition.symm

/-- Reading an input buffer does not introduce any additional serialization transform. -/
theorem initial_input_read (candidate : Submission) (program : Program)
    (input : Input candidate.sizes program) (address count : Nat)
    (bounded : address + count ≤ 2^64) :
    readBuffer (candidate.initialState program input) address count =
      BitVec.ofNat (8*count) (∑ j ∈ Finset.range count,
        (inputByte candidate program input (address+j)).toNat * 2^(8*j)) := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [initial_input_byte candidate program input _ (by have := Finset.mem_range.mp hj; omega)]

private theorem sum_digits (value count : Nat) :
    (∑ i ∈ Finset.range count, (value / 2^(8*i) % 256) * 2^(8*i)) = value % 2^(8*count) := by
  induction count with
  | zero => simp only [Finset.sum_range_zero, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | succ count ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    simp only [Nat.reducePow, Nat.mul_comm]

/-- Little-endian serialization and reading recover the exact requested bit slice.
This holds for arbitrary widths, including the full serialized private state. -/
theorem read_serialized_slice {width : Nat} (state : MachineState) (value : BitVec width)
    (address offset count : Nat)
    (bytes : ∀ j < count, state.getByte (BitVec.ofNat 64 (address+j)) =
      value.extractLsb' (8*(offset+j)) 8) :
    readBuffer state address count = value.extractLsb' (8*offset) (8*count) := by
  apply BitVec.eq_of_toNat_eq
  simp only [readBuffer, BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
  have terms : (∑ j ∈ Finset.range count,
      (state.getByte (BitVec.ofNat 64 (address+j))).toNat * 2^(8*j)) =
      (∑ j ∈ Finset.range count,
        ((value.toNat / 2^(8*offset)) / 2^(8*j) % 256) * 2^(8*j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [bytes j (Finset.mem_range.mp hj)]
    simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow, Nat.mul_add,
      Nat.pow_add, Nat.div_div_eq_div_mul]
    rfl
  rw [terms, sum_digits, Nat.mod_mod]

private def byteSum (bytes : Nat → Byte) (count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (bytes i).toNat * 2^(8*i)

private theorem byte_sum_bound (bytes : Nat → Byte) (count : Nat) :
    byteSum bytes count < 2^(8*count) := by
  induction count with
  | zero => simp [byteSum]
  | succ count ih =>
    have byteBound := (bytes count).isLt
    have termBound := Nat.mul_le_mul_right (2^(8*count))
      (show (bytes count).toNat ≤ 255 by omega)
    rw [byteSum, Finset.sum_range_succ]
    change byteSum bytes count + _ < _
    rw [Nat.mul_succ, Nat.pow_add]
    norm_num only [Nat.reducePow]
    omega

private theorem byte_sum_add (bytes : Nat → Byte) (left right : Nat) :
    byteSum bytes (left+right) = byteSum bytes left +
      2^(8*left) * byteSum (fun i => bytes (left+i)) right := by
  unfold byteSum
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.mul_add, Nat.pow_add]
  ring

private theorem byte_sum_slice (bytes : Nat → Byte) (total offset count : Nat)
    (inside : offset+count ≤ total) :
    byteSum bytes total / 2^(8*offset) % 2^(8*count) =
      byteSum (fun i => bytes (offset+i)) count := by
  conv_lhs => rw [show total = offset + (count + (total-(offset+count))) by omega]
  rw [byte_sum_add, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (byte_sum_bound bytes offset), Nat.zero_add, byte_sum_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (byte_sum_bound _ count)]

/-- Slicing a serialized memory buffer recovers the corresponding original bytes.
The proof is independent of buffer size, so it also applies to the large trapdoor. -/
theorem read_buffer_slice (state : MachineState) (address total offset count : Nat)
    (inside : offset+count ≤ total) :
    (readBuffer state address total).extractLsb' (8*offset) (8*count) =
      readBuffer state (address+offset) count := by
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat (8*count)
    ((BitVec.ofNat (8*total)
      (byteSum (fun i => state.getByte (BitVec.ofNat 64 (address+i))) total)).toNat >>> (8*offset))).toNat =
    (BitVec.ofNat (8*count)
      (byteSum (fun i => state.getByte (BitVec.ofNat 64 (address+offset+i))) count)).toNat
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (byte_sum_bound _ total), Nat.mod_eq_of_lt (byte_sum_bound _ count)]
  rw [byte_sum_slice _ _ _ _ inside]
  simp only [Nat.add_assoc]

/-- An individual byte survives memory serialization exactly. -/
theorem read_buffer_byte (state : MachineState) (address total offset : Nat)
    (inside : offset < total) :
    (readBuffer state address total).extractLsb' (8*offset) 8 =
      state.getByte (BitVec.ofNat 64 (address+offset)) := by
  have slice := read_buffer_slice state address total offset 1 (by omega)
  simpa [readBuffer, Finset.sum_range_succ] using slice

end CommitGolfCandidate
