import CommitGolfCandidate.C3LeafModel
import CommitGolfCandidate.TwoPermutationLeafAccess

/-! # Memory and syscall facts for the 3c1p commit loop

The 64-byte compression input at an aligned word is `packWords8` of the eight memory words there,
and a 32-byte compression reply written at an aligned word is the window `digestWords reply`.
`execute_compression_on` is the trusted compression syscall step for any image. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option autoImplicit false

theorem c3_read_digest (state : MachineState) (start : Nat) :
    readBuffer state (8 * start) 32 = packDigestWords (window (memoryView state) start : Words 4) := by
  rw [CommitGolfCandidate.read_digest_words state (8 * start) (by omega)]
  simp only [packDigestWords, window, memoryView, wordAddress]
  congr 3

theorem c3_read_compression (state : MachineState) (start : Nat) :
    readBuffer state (8 * start) 64 = packWords8 (window (memoryView state) start : Words 8) := by
  rw [CommitGolfCandidate.read_compression_halves state (8 * start) (by omega),
    show 8 * start + 32 = 8 * (start + 4) by omega, c3_read_digest, c3_read_digest]
  unfold packWords8
  congr 2
  all_goals funext k
  all_goals simp only [window]
  all_goals rw [show start + 4 + k.val = start + (k.val + 4) by omega]

private theorem c3_read_one_word (state : MachineState) (word : Nat) :
    readBuffer state (8 * word) 8 = memoryView state word := by
  have sliced := CommitGolfCandidate.read_buffer_slice state (8 * word) 32 0 8 (by decide)
  have extracted := CommitGolfCandidate.read_digest_word state (8 * word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero, memoryView, wordAddress] using sliced.symm.trans extracted

theorem compression_write_memory (state : MachineState) (dst word : Nat) (reply : BitVec 256)
    (dstBound : dst + 4 ≤ 2 ^ 33) (wordBound : word < 2 ^ 33) :
    memoryView (writeBits state (wordAddress dst) reply) word =
      writeWindow (memoryView state) dst (digestWords reply) word := by
  let written := writeBits state (wordAddress dst) reply
  rw [← c3_read_one_word written]
  by_cases inside : dst ≤ word ∧ word < dst + 4
  · rw [writeWindow, dite_eq_left inside]
    change readBuffer written (8 * word) 8 = reply.extractLsb' (64 * (word - dst)) 64
    rw [show 64 * (word - dst) = 8 * (8 * (word - dst)) by omega]
    apply CommitGolfCandidate.read_serialized_slice written reply (8 * word) (8 * (word - dst)) 8
    intro index limit
    have byte := CommitGolfCandidate.write_bits_byte state (wordAddress dst) reply (8 * (word - dst) + index)
      (by omega) (by decide)
    simpa only [written, wordAddress, ← BitVec.ofNat_add,
      show 8 * dst + (8 * (word - dst) + index) = 8 * word + index by omega] using byte
  · rw [writeWindow, dite_eq_right inside, ← c3_read_one_word state]
    apply congrArg (BitVec.ofNat 64)
    apply Finset.sum_congr rfl
    intro index present
    have indexBound := Finset.mem_range.mp present
    have separate : ∀ offset < 32, BitVec.ofNat 64 (8 * word + index) ≠
        wordAddress dst + BitVec.ofNat 64 offset := by
      intro offset offsetBound equal
      have numeric := congrArg BitVec.toNat equal
      rw [wordAddress, ← BitVec.ofNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * word + index < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega : 8 * dst + offset < 2 ^ 64)] at numeric
      omega
    rw [CommitGolfCandidate.write_bits_byte_outside state (wordAddress dst) _ reply (by simpa using separate)]

theorem oracle_input_compression_on (state : MachineState) (src dst : Nat)
    (srcBound : src + 8 ≤ 2 ^ 33) (dstBound : dst + 4 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (size : state.getReg .x11 = 64) (primitive : state.getReg .x13 = 0) :
    oracleInput state = some (.inl (readBuffer state (8 * src) 64)) := by
  have srcValue := word_address_value (word := src) (by omega)
  have dstValue := word_address_value (word := dst) (by omega)
  have fitsSrc : 8 * src + 64 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have fitsDst : 8 * dst + 32 ≤ MEMORY_BYTES := by unfold MEMORY_BYTES; omega
  have kind : (state.getReg .x13).toNat = 0 := by rw [primitive]; rfl
  unfold oracleInput
  dsimp only
  rw [kind]
  simp [input, output, size, srcValue, dstValue, rangeValid, fitsSrc, fitsDst,
    COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH]

theorem execute_compression_on (image : Image) (fuel : Nat) (state : MachineState) (allowCoins : Bool)
    (src dst : Nat) (srcBound : src + 8 ≤ 2 ^ 33) (dstBound : dst + 4 ≤ 2 ^ 33)
    (input : state.getReg .x10 = wordAddress src) (output : state.getReg .x12 = wordAddress dst)
    (selector : state.getReg .x5 = 0) (size : state.getReg .x11 = 64) (primitive : state.getReg .x13 = 0)
    (fetched : fetch image state = some (.base .ECALL)) :
    execute image (fuel + 1) state allowCoins = (do
      let answer ← World.query (.inr (.inl (readBuffer state (8 * src) 64)))
      let result ← execute image fuel (writeBits state (wordAddress dst) answer) allowCoins
      return result.charge 8 1) := by
  have ready := oracle_input_compression_on state src dst srcBound dstBound input output size primitive
  simp only [execute, fetched, selector, ↓reduceIte, ready, output, writeOracleAnswer, oracleCycles,
    COMPRESSION_CYCLES]

theorem word_access (start offset : Nat) (bound : start + offset < 2^33) :
    accessValid (wordAddress start + BitVec.ofNat 64 (8 * offset)) 8 = true :=
  leaf_word_access start offset bound

theorem word_address_plus (a b : Nat) : wordAddress a + BitVec.ofNat 64 (8 * b) = wordAddress (a + b) :=
  (wordAddress_add a b).symm


/-! ### Instruction effects on an abstract state (never unfold a written state) -/

theorem address_up (a n : Nat) : wordAddress a + BitVec.ofNat 64 (8 * n) = wordAddress (a + n) :=
  (wordAddress_add a n).symm

/-! Register effects of the ADDI forms used here, on an abstract state (never unfold a written state). -/
theorem addi_self (s : MachineState) (r : Reg) (imm : BitVec 12) (h : r ≠ .x0) :
    (execInstrBr s (.ADDI r r imm)).getReg r = s.getReg r + signExtend12 imm := by
  cases r <;> first | exact absurd rfl h | rfl

theorem addi_from (s : MachineState) (rd rs : Reg) (imm : BitVec 12) (h : rd ≠ .x0) :
    (execInstrBr s (.ADDI rd rs imm)).getReg rd = s.getReg rs + signExtend12 imm := by
  cases rd <;> cases rs <;> first | exact absurd rfl h | rfl

theorem addi_other (s : MachineState) (rd rs r : Reg) (imm : BitVec 12) (h : r ≠ rd) :
    (execInstrBr s (.ADDI rd rs imm)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem addi_pc (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs imm)).pc = s.pc + 4 := rfl

theorem address_down (a n : Nat) (imm : BitVec 12) (value : signExtend12 imm = BitVec.ofNat 64 (2 ^ 64 - 8 * n))
    (room : n ≤ a) (small : 8 * n ≤ 2 ^ 64) :
    wordAddress a + signExtend12 imm = wordAddress (a - n) := by
  rw [value, wordAddress, wordAddress, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 8 * a + (2 ^ 64 - 8 * n) = 8 * (a - n) + 2 ^ 64 by omega, Nat.add_mod_right]

theorem addi_mem (s : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs imm)).mem = s.mem := by
  cases rd <;> rfl

theorem memoryView_congr {s t : MachineState} (h : s.mem = t.mem) : memoryView s = memoryView t := by
  funext w; change s.mem _ = t.mem _; rw [h]

/-! Effects of the store, load and add-immediate forms used here, on an abstract state. -/
theorem sd_mem (s : MachineState) (b src : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD b src imm)).mem = (s.setMem (s.getReg b + signExtend12 imm) (s.getReg src)).mem := rfl

theorem sd_reg (s : MachineState) (b src r : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD b src imm)).getReg r = s.getReg r := by
  cases r <;> rfl

theorem sd_pc (s : MachineState) (b src : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD b src imm)).pc = s.pc + 4 := rfl

theorem ld_same (s : MachineState) (rd b : Reg) (imm : BitVec 12) (h : rd ≠ .x0) :
    (execInstrBr s (.LD rd b imm)).getReg rd = s.getMem (s.getReg b + signExtend12 imm) := by
  cases rd <;> first | exact absurd rfl h | rfl

theorem ld_other (s : MachineState) (rd b r : Reg) (imm : BitVec 12) (h : r ≠ rd) :
    (execInstrBr s (.LD rd b imm)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)]

theorem ld_mem (s : MachineState) (rd b : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd b imm)).mem = s.mem := by
  cases rd <;> rfl

theorem ld_pc (s : MachineState) (rd b : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd b imm)).pc = s.pc + 4 := rfl

theorem view_store (s : MachineState) (address w : Nat) (value : Word)
    (addressBound : address < 2 ^ 61) (wordBound : w < 2 ^ 61) :
    memoryView (s.setMem (wordAddress address) value) w = writeWord (memoryView s) address value w :=
  memory_at_store addressBound wordBound


end TwoPermutationPrototype.RV64.C3Leaves
