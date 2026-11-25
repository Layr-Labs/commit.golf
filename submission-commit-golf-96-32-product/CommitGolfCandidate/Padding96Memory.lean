import CommitGolfCandidate.MemoryCore
import CommitGolfCandidate.WriteMemoryCore

/-! The 96-byte adapter saves, zeroes, and restores its final 32 bytes.
Its input is the injectively padded binary encoding, and its only lasting memory
change is the oracle reply. These statements refer to the interpreter's memory. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def padMemory (state : MachineState) (source : Word) : MachineState :=
  (((state.setMem (source+64) 0).setMem (source+72) 0).setMem (source+80) 0).setMem (source+88) 0

def restorePadding (state original : MachineState) (source : Word) : MachineState :=
  (((state.setMem (source+64) (original.getMem (source+64))).setMem
    (source+72) (original.getMem (source+72))).setMem
    (source+80) (original.getMem (source+80))).setMem
    (source+88) (original.getMem (source+88))

private theorem offset_ne (source : Word) (left right : Nat)
    (leftBound : left < 2^64) (rightBound : right < 2^64) (different : left ≠ right) :
    source + BitVec.ofNat 64 left ≠ source + BitVec.ofNat 64 right := by
  intro equal
  have canceled := congrArg (fun value : Word => value-source) equal
  simp only [BitVec.add_comm source, BitVec.add_sub_cancel] at canceled
  have natural := congrArg BitVec.toNat canceled
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] at natural
  exact different natural

/-- Zeroing the extra block preserves every word of the original 64-byte payload. -/
theorem pad_memory_before (state : MachineState) (source : Word) (offset : Nat)
    (inside : offset < 64) :
    (padMemory state source).getMem (source + BitVec.ofNat 64 offset) =
      state.getMem (source + BitVec.ofNat 64 offset) := by
  unfold padMemory
  erw [MachineState.getMem_setMem_ne (offset_ne source offset 88 (by omega) (by decide) (by omega)),
    MachineState.getMem_setMem_ne (offset_ne source offset 80 (by omega) (by decide) (by omega)),
    MachineState.getMem_setMem_ne (offset_ne source offset 72 (by omega) (by decide) (by omega)),
    MachineState.getMem_setMem_ne (offset_ne source offset 64 (by omega) (by decide) (by omega))]

theorem pad_memory_zero (state : MachineState) (source : Word) (word : Nat)
    (inside : word < 4) :
    (padMemory state source).getMem (source + BitVec.ofNat 64 (64+8*word)) = 0 := by
  interval_cases word <;>
    simp [padMemory, MachineState.getMem, MachineState.setMem]

/-- The machine's actual 96-byte read equals the padded abstract compression input. -/
theorem pad_memory_read (state : MachineState) (source : Nat) (aligned : source % 8 = 0) :
    readBuffer (padMemory state (BitVec.ofNat 64 source)) source 96 =
      padInput (readBuffer state source 64) := by
  have zero : readBuffer (padMemory state (BitVec.ofNat 64 source)) (source+64) 32 = 0 := by
    rw [read_digest_words _ _ (by omega)]
    have w0 := pad_memory_zero state (BitVec.ofNat 64 source) 0 (by decide)
    have w1 := pad_memory_zero state (BitVec.ofNat 64 source) 1 (by decide)
    have w2 := pad_memory_zero state (BitVec.ofNat 64 source) 2 (by decide)
    have w3 := pad_memory_zero state (BitVec.ofNat 64 source) 3 (by decide)
    simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero, ← BitVec.ofNat_add] at w0 w1 w2 w3
    simp only [Nat.add_assoc, Nat.reduceAdd, w0, w1, w2, w3]
    rfl
  have half (offset : Nat) (choice : offset = 0 ∨ offset = 32) :
      readBuffer (padMemory state (BitVec.ofNat 64 source)) (source+offset) 32 =
        readBuffer state (source+offset) 32 := by
    apply read_digest_congr _ _ _ (by rcases choice with rfl | rfl <;> omega)
    intro i hi
    have unchanged := pad_memory_before state (BitVec.ofNat 64 source) (offset+8*i)
      (by rcases choice with rfl | rfl <;> omega)
    simpa only [← BitVec.ofNat_add, Nat.add_assoc] using unchanged
  rw [read_compression_padding, zero, padInput,
    read_compression_halves _ _ aligned, read_compression_halves _ _ aligned,
    half 32 (Or.inr rfl)]
  simpa only [Nat.add_zero] using congrArg (fun value : BitVec 256 =>
    (0 : BitVec 256) ++ (readBuffer state (source+32) 32 ++ value)) (half 0 (Or.inl rfl))

private theorem set_mem_commute (state : MachineState) (left right a b : Word)
    (different : left ≠ right) :
    (state.setMem left a).setMem right b = (state.setMem right b).setMem left a := by
  simp only [MachineState.setMem]
  congr 1
  funext query
  by_cases l : query = left <;> by_cases r : query = right <;> simp_all

private theorem set_byte_set_mem (state : MachineState) (address query value : Word)
    (byte : Byte) (different : query ≠ alignToDword address) :
    (state.setMem query value).setByte address byte =
      (state.setByte address byte).setMem query value := by
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne different.symm]
  exact set_mem_commute _ _ _ _ _ different

/-- A disjoint word store commutes with the byte-wise oracle writer. -/
theorem write_bits_set_mem {bits : Nat} (state : MachineState) (address query value : Word)
    (answer : BitVec bits)
    (separate : ∀ i < (bits+7)/8, query ≠ alignToDword (address+BitVec.ofNat 64 i)) :
    writeBits (state.setMem query value) address answer =
      (writeBits state address answer).setMem query value := by
  have commute (indices : List Nat) (state : MachineState)
      (outside : ∀ i ∈ indices, query ≠ alignToDword (address+BitVec.ofNat 64 i)) :
      indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) (state.setMem query value) =
      (indices.foldl (fun current i => current.setByte (address+BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2^(8*i)))) state).setMem query value := by
    induction indices generalizing state with
    | nil => rfl
    | cons i rest ih =>
      rw [List.foldl_cons, set_byte_set_mem _ _ _ _ _ (outside i (by simp)),
        ih _ (fun j hj => outside j (by simp [hj]))]
      rfl
  unfold writeBits
  rw [commute _ state (fun i hi => separate i (List.mem_range.mp hi))]
  rfl

/-- Restoring the saved block cancels all temporary stores. -/
theorem restore_pad_memory (state : MachineState) (source : Word) :
    restorePadding (padMemory state source) state source = state := by
  simp only [restorePadding, padMemory, MachineState.setMem, MachineState.getMem]
  have same : (fun query =>
      if query == source+88 then state.mem (source+88) else
      if query == source+80 then state.mem (source+80) else
      if query == source+72 then state.mem (source+72) else
      if query == source+64 then state.mem (source+64) else
      if query == source+88 then 0 else if query == source+80 then 0 else
      if query == source+72 then 0 else if query == source+64 then 0 else state.mem query) =
      state.mem := by
    funext query
    by_cases h88 : query = source+88 <;> by_cases h80 : query = source+80 <;>
      by_cases h72 : query = source+72 <;> by_cases h64 : query = source+64 <;> simp_all
  rw [same]

/-- The adapter leaves exactly the reply write when the output avoids the padding. -/
theorem restore_padding_write (state : MachineState) (source destination : Word)
    (answer : BitVec 256)
    (separate : ∀ word < 4, ∀ byte < 32,
      source+BitVec.ofNat 64 (64+8*word) ≠
        alignToDword (destination+BitVec.ofNat 64 byte)) :
    restorePadding (writeBits (padMemory state source) destination answer) state source =
      writeBits state destination answer := by
  have s0 := separate 0 (by decide)
  have s1 := separate 1 (by decide)
  have s2 := separate 2 (by decide)
  have s3 := separate 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at s0 s1 s2 s3
  unfold restorePadding
  rw [← write_bits_set_mem _ _ _ _ _ s0, ← write_bits_set_mem _ _ _ _ _ s1,
    ← write_bits_set_mem _ _ _ _ _ s2, ← write_bits_set_mem _ _ _ _ _ s3]
  rw [show ((((padMemory state source).setMem (source+64) (state.getMem (source+64))).setMem
      (source+72) (state.getMem (source+72))).setMem
      (source+80) (state.getMem (source+80))).setMem
      (source+88) (state.getMem (source+88)) = state from restore_pad_memory state source]

end CommitGolfCandidate
