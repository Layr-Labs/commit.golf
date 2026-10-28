import CommitGolfCandidate.InputMemory

/-! Byte-exact syscall writes, including random salts and compression replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem byte_offset_bound (address : Word) : byteOffset address < 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem byte_address_parts (address : Word) :
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

private theorem extract_replace_byte (word : Word) (byte : Byte) (index : Nat) (inside : index < 8) :
    extractByte (replaceByte word index byte) index = byte := by
  interval_cases index <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit hb <;>
    interval_cases bit <;>
    simp [extractByte, replaceByte]

private theorem extract_replace_other (word : Word) (byte : Byte) (index other : Nat)
    (inside : index < 8) (otherInside : other < 8) (different : other ≠ index) :
    extractByte (replaceByte word index byte) other = extractByte word other := by
  interval_cases index <;> interval_cases other <;>
    first
    | exact (different rfl).elim
    | (apply BitVec.eq_of_getLsbD_eq
       intro bit hb
       interval_cases bit <;> simp [extractByte, replaceByte])

/-- A byte store changes exactly its addressed byte, even when two addresses share a word. -/
theorem set_byte_read (state : MachineState) (address query : Word) (byte : Byte) :
    (state.setByte address byte).getByte query =
      if query = address then byte else state.getByte query := by
  by_cases same : query = address
  · subst query
    simp only [MachineState.setByte, MachineState.getByte, MachineState.getMem_setMem_eq, if_true]
    exact extract_replace_byte _ _ _ (byte_offset_bound address)
  · rw [if_neg same]
    by_cases aligned : alignToDword query = alignToDword address
    · have different : byteOffset query ≠ byteOffset address := by
        intro offsets
        have parts := byte_address_parts query
        rw [aligned, offsets, byte_address_parts address] at parts
        exact same parts.symm
      simp only [MachineState.setByte, MachineState.getByte, aligned, MachineState.getMem_setMem_eq]
      exact extract_replace_other _ _ _ _ (byte_offset_bound address) (byte_offset_bound query) different
    · simp only [MachineState.setByte, MachineState.getByte, MachineState.getMem_setMem_ne aligned]

private theorem write_list_outside (state : MachineState) (address query : Word)
    (bytes : Nat → Byte) (indices : List Nat)
    (outside : ∀ i ∈ indices, query ≠ address+BitVec.ofNat 64 i) :
    (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i) (bytes i)) state).getByte query =
      state.getByte query := by
  induction indices generalizing state with
  | nil => rfl
  | cons i rest ih =>
    rw [List.foldl_cons, ih _ (fun j hj => outside j (by simp [hj])),
      set_byte_read, if_neg (outside i (by simp))]

/-- Byte-wise syscall writes preserve all bytes outside their output range. -/
theorem write_bits_byte_outside {bits : Nat} (state : MachineState) (address query : Word)
    (answer : BitVec bits)
    (outside : ∀ i < (bits+7)/8, query ≠ address+BitVec.ofNat 64 i) :
    (writeBits state address answer).getByte query = state.getByte query := by
  unfold writeBits
  change ((List.range ((bits+7)/8)).foldl _ state).getByte query = _
  exact write_list_outside state address query _ _ (fun i hi => outside i (List.mem_range.mp hi))

private theorem write_range_byte (state : MachineState) (address : Word)
    (bytes : Nat → Byte) (count index : Nat) (inside : index < count) (bounded : count ≤ 2^64) :
    ((List.range count).foldl
      (fun current i => current.setByte (address+BitVec.ofNat 64 i) (bytes i)) state).getByte
        (address+BitVec.ofNat 64 index) = bytes index := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, set_byte_read]
    by_cases last : index = count
    · subst index
      rw [if_pos rfl]
    · have distinct : address+BitVec.ofNat 64 index ≠ address+BitVec.ofNat 64 count := by
        intro equal
        have words := congrArg (fun value : Word => value-address) equal
        simp only [BitVec.add_comm address, BitVec.add_sub_cancel] at words
        have natural := congrArg BitVec.toNat words
        simp only [BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : index < 2^64),
          Nat.mod_eq_of_lt (by omega : count < 2^64)] at natural
        omega
      rw [if_neg distinct]
      exact ih (by omega) (by omega)

/-- Each syscall output byte is the corresponding low-endian slice of its reply. -/
theorem write_bits_byte {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (index : Nat) (inside : index < (bits+7)/8)
    (bounded : (bits+7)/8 ≤ 2^64) :
    (writeBits state address answer).getByte (address+BitVec.ofNat 64 index) =
      answer.extractLsb' (8*index) 8 := by
  unfold writeBits
  change ((List.range ((bits+7)/8)).foldl _ state).getByte _ = _
  rw [write_range_byte state address _ _ index inside bounded]
  simp only [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- Any complete digest within a syscall reply can be read back unchanged. -/
theorem write_bits_digest {bits : Nat} (state : MachineState) (address offset : Nat)
    (answer : BitVec bits) (inside : offset+32 ≤ (bits+7)/8)
    (bounded : (bits+7)/8 ≤ 2^64) :
    readBuffer (writeBits state (BitVec.ofNat 64 address) answer) (address+offset) 32 =
      answer.extractLsb' (8*offset) 256 := by
  apply read_serialized_slice
  intro j hj
  have written := write_bits_byte state (BitVec.ofNat 64 address) answer (offset+j) (by omega) bounded
  simpa only [BitVec.ofNat_add, Nat.add_assoc, BitVec.add_assoc] using written

/-- The writer's output memory depends only on input memory, not on registers or PC. -/
theorem write_bits_memory_congr {bits : Nat} (left right : MachineState) (address : Word)
    (answer : BitVec bits) (same : left.mem = right.mem) :
    (writeBits left address answer).mem = (writeBits right address answer).mem := by
  have preserved (indices : List Nat) (left right : MachineState) (same : left.mem = right.mem) :
      (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) left).mem =
      (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) right).mem := by
    induction indices generalizing left right with
    | nil => exact same
    | cons i rest ih =>
      simp only [List.foldl_cons]
      apply ih
      simp only [MachineState.setByte, MachineState.setMem, MachineState.getMem, same]
  exact preserved _ left right same

/-- A syscall write leaves an entirely disjoint readable buffer unchanged. -/
theorem write_bits_read_outside {bits : Nat} (state : MachineState) (answer : BitVec bits)
    (destination address count : Nat)
    (destinationBound : destination+(bits+7)/8 ≤ 2^64) (readBound : address+count ≤ 2^64)
    (separate : address+count ≤ destination ∨ destination+(bits+7)/8 ≤ address) :
    readBuffer (writeBits state (BitVec.ofNat 64 destination) answer) address count =
      readBuffer state address count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  have smaller := Finset.mem_range.mp hi
  have unchanged := write_bits_byte_outside state (BitVec.ofNat 64 destination)
    (BitVec.ofNat 64 (address+i)) answer (by
      intro j hj equal
      have numeric := congrArg BitVec.toNat equal
      rw [← BitVec.ofNat_add] at numeric
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : address+i < 2^64),
        Nat.mod_eq_of_lt (by omega : destination+j < 2^64)] at numeric
      rcases separate with before | after <;> omega)
  rw [unchanged]

end CommitGolfCandidate
