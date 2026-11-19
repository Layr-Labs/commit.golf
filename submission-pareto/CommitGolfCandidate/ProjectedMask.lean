import CommitGolfCandidate.ProjectedCompression
import CommitGolfCandidate.CapCompressionStep
import CommitGolfCandidate.WriteMemory

/-! Clearing the top 18 bits of a compression reply's top word leaves the
stored 238-bit internal digest. This segment serves both commit and checker images. -/
namespace CommitGolfCandidate.ShortTree
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] readBuffer

/-- Keeps the low 46 bits of the top reply word: reply bits 192 to 237. -/
def digestMaskWord : Word := 0x00003FFFFFFFFFFF#64

theorem top_word_mask (x : BitVec 256) :
    x.extractLsb' 192 64 &&& digestMaskWord = (padLow x).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  simp only [digestMaskWord, padLow, low240, lowBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_and]
  interval_cases bit <;> simp

theorem top_word_shift (x : BitVec 256) :
    (x.extractLsb' 192 64 <<< 18) >>> 18 = (padLow x).extractLsb' 192 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  simp only [padLow, low240, lowBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  interval_cases bit <;> simp

private theorem low_words (x : BitVec 256) (w : Nat) (hw : w < 3) :
    x.extractLsb' (64*w) 64 = (padLow x).extractLsb' (64*w) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hb
  have inside : 64*w+bit < 238 := by omega
  have inside' : 64*w+bit < 240 := by omega
  simp only [padLow, low240, lowBits, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb,
    decide_true, Bool.true_and, inside, inside', if_true]
  simp [inside]

private theorem output_word (state : MachineState) (base k : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (inside : k < 4) :
    (writeBits state (BitVec.ofNat 64 base) answer).getMem (BitVec.ofNat 64 (base+8*k)) =
      answer.extractLsb' (64*k) 64 := by
  have written := write_bits_digest state base 0 answer (by decide) (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, BitVec.extractLsb'_eq_self] at written
  rw [← read_digest_word _ _ _ aligned inside, written]

private theorem byte_offset (a : Word) : byteOffset a = a.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

private theorem split_address (a : Word) : alignToDword a + BitVec.ofNat 64 (byteOffset a) = a := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint]
  ext i
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  cases h : (7#64)[i] <;> simp

private theorem word_address (base i : Nat) (aligned : base % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (base+i)) = BitVec.ofNat 64 (base+8*(i/8)) := by
  have offset : byteOffset (BitVec.ofNat 64 (base+i)) = i%8 := by
    rw [byte_offset, BitVec.toNat_ofNat]; omega
  have parts := split_address (BitVec.ofNat 64 (base+i))
  rw [offset] at parts
  have joined : BitVec.ofNat 64 (base+8*(i/8)) + BitVec.ofNat 64 (i%8) =
      BitVec.ofNat 64 (base+i) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have eq := congrArg (fun v : Word => v - BitVec.ofNat 64 (i%8)) (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq

/-- Storing the masked top word reproduces the memory the padded oracle
response would have written, including every lookup outside that reply. -/
theorem masked_reply_memory (state : MachineState) (base : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) (bound : base + 32 ≤ 2^64) :
    ((writeBits state (BitVec.ofNat 64 base) answer).setMem
      (BitVec.ofNat 64 (base+24)) ((padLow answer).extractLsb' 192 64)).mem =
    (writeBits state (BitVec.ofNat 64 base) (padLow answer)).mem := by
  funext q
  change (((writeBits state (BitVec.ofNat 64 base) answer).setMem _ _).getMem q) = _
  by_cases last : q = BitVec.ofNat 64 (base+24)
  · subst q
    rw [MachineState.getMem_setMem_eq]
    change _ = (writeBits state _ _).getMem (BitVec.ofNat 64 (base+8*3))
    rw [output_word state base 3 _ aligned (by decide)]
  · rw [MachineState.getMem_setMem_ne last]
    by_cases someWord : ∃ k < 4, q = BitVec.ofNat 64 (base+8*k)
    · obtain ⟨k, hk, rfl⟩ := someWord
      change _ = (writeBits state _ _).getMem _
      rw [output_word state base k _ aligned hk, output_word state base k _ aligned hk]
      apply low_words
      by_contra! large
      have eq : k=3 := by omega
      exact last (by rw [eq])
    · have away : ∀ i < 32, q ≠ alignToDword (BitVec.ofNat 64 base + BitVec.ofNat 64 i) := by
        intro i hi eq; apply someWord
        exact ⟨i/8, by omega, eq.trans (by rw [← BitVec.ofNat_add, word_address base i aligned])⟩
      exact (writeBits_memory_outside state _ q answer away).trans
        (writeBits_memory_outside state _ q (padLow answer) away).symm

/-- The written reply's top word, as read back by an aligned load. -/
theorem reply_top_word (state : MachineState) (base : Nat) (answer : BitVec 256)
    (aligned : base % 8 = 0) :
    (writeBits state (BitVec.ofNat 64 base) answer).getMem (BitVec.ofNat 64 (base+24)) =
      answer.extractLsb' 192 64 :=
  output_word state base 3 answer aligned (by decide)

theorem write_frame {bits : Nat} (state : MachineState) (address : Word) (answer : BitVec bits) :
    writeBits state address answer =
      { state with mem := (writeBits state address answer).mem, pc := state.pc+4 } := by
  let put (s : MachineState) (i : Nat) := s.setByte (address + BitVec.ofNat 64 i)
      (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))
  have onlyMemory (is : List Nat) (s : MachineState) :
      is.foldl put s = { s with mem := (is.foldl put s).mem } := by
    induction is generalizing s with
    | nil => rfl
    | cons i rest ih => exact ih (put s i)
  unfold writeBits
  change ((List.range ((bits+7)/8)).foldl put state).setPC (state.pc+4) = _
  rw [onlyMemory (List.range ((bits+7)/8)) state]
  rfl

end CommitGolfCandidate.ShortTree
