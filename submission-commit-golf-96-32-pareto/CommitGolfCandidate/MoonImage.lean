import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨2348810240, 11140077536⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 6643781664, 6777999392, 11072966688⟩ := rfl

theorem commit_dataBase : dataBase (submission.image .commit) = 68719476736 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem opening_dataBase : dataBase (submission.image .opening) = 68719476736 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem check_dataBase : dataBase (submission.image .check) = 68719476736 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem submission_admission : submission.Admission := by
  intro program
  cases program
  · refine ⟨⟨?_, ?_, ?_⟩, by decide, by decide⟩
    · simp only [submission, MoonArtifact.submission, Image.byteSize, ArtifactEncoding.length_decode,
        MAX_PROGRAM_BYTES]
      decide
    · intro b hb
      rw [commit_dataBase]
      simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      decide
  · refine ⟨⟨?_, ?_, ?_⟩, by decide, by decide⟩
    · simp only [submission, MoonArtifact.submission, Image.byteSize, ArtifactEncoding.length_decode,
        MAX_PROGRAM_BYTES]
      decide
    · intro b hb
      rw [opening_dataBase]
      simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      decide
  · refine ⟨⟨?_, ?_, ?_⟩, by decide, by decide⟩
    · simp only [submission, MoonArtifact.submission, Image.byteSize, ArtifactEncoding.length_decode,
        MAX_PROGRAM_BYTES]
      decide
    · intro b hb
      rw [check_dataBase]
      simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [submission, MoonArtifact.submission, Layout.buffers, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      decide

/-! ### Generic Packed Fetch Helpers -/

theorem getElem?_decode (bits : Nat) {count : Nat} (packed : ArtifactEncoding.Packed count)
    (index : Nat) (inside : index < count) :
    (ArtifactEncoding.decode bits packed)[index]? = some (packed.get bits ⟨index, inside⟩) := by
  simp [ArtifactEncoding.decode, inside]

theorem fetch_of_packed {count : Nat} (code : ArtifactEncoding.Packed count) (data : List Byte)
    (state : MachineState) (idx : Nat) (inside : idx < count)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (instr : Instruction)
    (hdec : decodeInstruction (code.get 32 ⟨idx, inside⟩) = some instr)
    (hsmall : 0x1000 + 4 * idx < 2 ^ 64 := by omega) :
    fetch ⟨ArtifactEncoding.decode 32 code, data⟩ state = some instr := by
  unfold fetch
  have hpc_nat : state.pc.toNat = 0x1000 + 4 * idx := by
    rw [hpc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  have hge : 0x1000 ≤ state.pc.toNat := by omega
  have hmod : state.pc.toNat % 4 = 0 := by omega
  have hidx : (state.pc.toNat - 0x1000) / 4 = idx := by omega
  simp only [hge, hmod, and_self, ite_true, hidx, getElem?_decode 32 code idx inside, hdec]

theorem fetch_of_packed_word {count : Nat} (code : ArtifactEncoding.Packed count) (data : List Byte)
    (state : MachineState) (idx : Nat) (inside : idx < count) (w : BitVec 32)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hword : code.get 32 ⟨idx, inside⟩ = w)
    (instr : Instruction)
    (hdec : decodeInstruction w = some instr)
    (hsmall : 0x1000 + 4 * idx < 2 ^ 64 := by omega) :
    fetch ⟨ArtifactEncoding.decode 32 code, data⟩ state = some instr := by
  refine fetch_of_packed code data state idx inside hpc instr ?_ hsmall
  rw [hword, hdec]

private def instDecEqInstruction : DecidableEq Instruction := fun a b =>
  match a, b with
  | .base i1, .base i2 =>
      if h : i1 = i2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .word o1 d1 s1 t1, .word o2 d2 s2 t2 =>
      if h : o1 = o2 ∧ d1 = d2 ∧ s1 = s2 ∧ t1 = t2 then
        isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl⟩; rfl)
      else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl, rfl⟩)
  | .sraiw d1 s1 sh1, .sraiw d2 s2 sh2 =>
      if h : d1 = d2 ∧ s1 = s2 ∧ sh1 = sh2 then
        isTrue (by rcases h with ⟨rfl, rfl, rfl⟩; rfl)
      else isFalse (by intro heq; cases heq; exact h ⟨rfl, rfl, rfl⟩)
  | .base _, .word .. | .base _, .sraiw .. | .word .., .base _ | .word .., .sraiw ..
  | .sraiw .., .base _ | .sraiw .., .word .. => isFalse (by intro h; cases h)

local instance : DecidableEq Instruction := instDecEqInstruction

/-! ### Commit Program: Constant-Body Repeating Bulk Loops -/

def randPairWord : Nat → BitVec 32
  | 0 => 0x00000073#32
  | 1 => 0x0b850513#32
  | _ => 0#32

def randPairInstr : Nat → Instruction
  | 0 => .base .ECALL
  | 1 => .base (.ADDI .x10 .x10 (184#12))
  | _ => .base .EBREAK

theorem decode_randPairWord (j : Fin 2) :
    decodeInstruction (randPairWord j.val) = some (randPairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_rand_words_0 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨16 + 2 * (0 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_1 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨16 + 2 * (128 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_2 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨16 + 2 * (256 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_3 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨16 + 2 * (384 + k.val) + j.val, by omega⟩ = randPairWord j.val := by
  revert k j; decide

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 512) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (16 + 2 * k + j) (by omega)
    (randPairWord j) hpc _ (randPairInstr j) (decode_randPairWord ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_rand_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    by_cases h1 : k < 256
    · have := commit_fetch_rand_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
      simpa [show 128 + (k - 128) = k by omega] using this
    ·
      by_cases h2 : k < 384
      · have := commit_fetch_rand_words_2 ⟨k - 256, by omega⟩ ⟨j, hj⟩
        simpa [show 256 + (k - 256) = k by omega] using this
      ·
        have := commit_fetch_rand_words_3 ⟨k - 384, by omega⟩ ⟨j, hj⟩
        simpa [show 384 + (k - 384) = k by omega] using this

def leaf0Word : Nat → BitVec 32
  | 0 => 0x10050513#32
  | 1 => 0x04050613#32
  | 2 => 0x00000073#32
  | _ => 0#32

def leaf0Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (256#12))
  | 1 => .base (.ADDI .x12 .x10 (64#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf0Word (j : Fin 3) :
    decodeInstruction (leaf0Word j.val) = some (leaf0Instr j.val) := by
  revert j; decide

private theorem commit_fetch_leaf0_words_0 (k : Fin 128) (j : Fin 3) :
    MoonArtifact.commitCode.get 32 ⟨1051 + 3 * (0 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

private theorem commit_fetch_leaf0_words_1 (k : Fin 128) (j : Fin 3) :
    MoonArtifact.commitCode.get 32 ⟨1051 + 3 * (128 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 256) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1051 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (1051 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_leaf0_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf0_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
    simpa [show 128 + (k - 128) = k by omega] using this

def leaf12PairWord : Nat → BitVec 32
  | 0 => 0x0a050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | 3 => 0x06050513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | 6 => 0x0a050513#32
  | 7 => 0x05860613#32
  | 8 => 0x00000073#32
  | 9 => 0x06050513#32
  | 10 => 0x02060613#32
  | 11 => 0x00000073#32
  | _ => 0#32

def leaf12PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (160#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (96#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | 6 => .base (.ADDI .x10 .x10 (160#12))
  | 7 => .base (.ADDI .x12 .x12 (88#12))
  | 8 => .base .ECALL
  | 9 => .base (.ADDI .x10 .x10 (96#12))
  | 10 => .base (.ADDI .x12 .x12 (32#12))
  | 11 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf12PairWord (j : Fin 12) :
    decodeInstruction (leaf12PairWord j.val) = some (leaf12PairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_leaf12_words_0 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨1828 + 12 * (0 + k.val) + j.val, by omega⟩ = leaf12PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_leaf12_words_1 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨1828 + 12 * (32 + k.val) + j.val, by omega⟩ = leaf12PairWord j.val := by
  revert k j; decide

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1828 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (1828 + 12 * k + j) (by omega)
    (leaf12PairWord j) hpc _ (leaf12PairInstr j) (decode_leaf12PairWord ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_leaf12_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf12_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

def leaf3PairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | 3 => 0x05850513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | _ => 0#32

def leaf3PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (88#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_leaf3PairWord (j : Fin 6) :
    decodeInstruction (leaf3PairWord j.val) = some (leaf3PairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_leaf3_words_0 (k : Fin 64) (j : Fin 6) :
    MoonArtifact.commitCode.get 32 ⟨2605 + 6 * (0 + k.val) + j.val, by omega⟩ = leaf3PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_leaf3_words_1 (k : Fin 64) (j : Fin 6) :
    MoonArtifact.commitCode.get 32 ⟨2605 + 6 * (64 + k.val) + j.val, by omega⟩ = leaf3PairWord j.val := by
  revert k j; decide

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (2605 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (2605 + 6 * k + j) (by omega)
    (leaf3PairWord j) hpc _ (leaf3PairInstr j) (decode_leaf3PairWord ⟨j, hj⟩)
  by_cases h0 : k < 64
  · simpa using commit_fetch_leaf3_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf3_words_1 ⟨k - 64, by omega⟩ ⟨j, hj⟩
    simpa [show 64 + (k - 64) = k by omega] using this

def q3StepWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | _ => 0#32

def q3StepInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_q3StepWord (j : Fin 3) :
    decodeInstruction (q3StepWord j.val) = some (q3StepInstr j.val) := by
  revert j; decide

private theorem commit_fetch_q3_words_0 (k : Fin 128) (j : Fin 3) :
    MoonArtifact.commitCode.get 32 ⟨3381 + 3 * (0 + k.val) + j.val, by omega⟩ = q3StepWord j.val := by
  revert k j; decide

private theorem commit_fetch_q3_words_1 (k : Fin 128) (j : Fin 3) :
    MoonArtifact.commitCode.get 32 ⟨3381 + 3 * (128 + k.val) + j.val, by omega⟩ = q3StepWord j.val := by
  revert k j; decide

theorem commit_fetch_q3 (state : MachineState) (k j : Nat) (hk : k < 256) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (3381 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (q3StepInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (3381 + 3 * k + j) (by omega)
    (q3StepWord j) hpc _ (q3StepInstr j) (decode_q3StepWord ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_q3_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_q3_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
    simpa [show 128 + (k - 128) = k by omega] using this

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (192#12))
  | 4 => .base (.SLLI .x6 .x6 (11#6))
  | 5 => .base (.SLLI .x6 .x6 (11#6))
  | 6 => .base (.ADDI .x6 .x6 (0#12))
  | 7 => .base (.ADD .x18 .x9 .x6)
  | 8 => .base (.ADDI .x5 .x0 (2#12))
  | 9 => .base (.ADDI .x10 .x18 (72#12))
  | 10 => .base (.ADDI .x11 .x0 (40#12))
  | 11 => .base (.ADDI .x6 .x0 (368#12))
  | 12 => .base (.SLLI .x6 .x6 (11#6))
  | 13 => .base (.SLLI .x6 .x6 (11#6))
  | 14 => .base (.ADDI .x6 .x6 (72#12))
  | 15 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr (i : Fin 16) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 16)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  have h := decode_commitPrefixInstr ⟨idx - 0, by omega⟩
  have heq : 0 + (idx - 0) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid0Instr : Nat → Instruction
  | 1040 => .base (.BNE .x10 .x19 (4096#13))
  | 1041 => .base (.ADDI .x5 .x0 (0#12))
  | 1042 => .base (.ADDI .x11 .x0 (96#12))
  | 1043 => .base (.ADDI .x13 .x0 (0#12))
  | 1044 => .base (.ADDI .x10 .x8 (3840#12))
  | 1045 => .base (.ADDI .x6 .x0 (1023#12))
  | 1046 => .base (.SLLI .x6 .x6 (11#6))
  | 1047 => .base (.ADDI .x6 .x6 (2047#12))
  | 1048 => .base (.SLLI .x6 .x6 (11#6))
  | 1049 => .base (.ADDI .x6 .x6 (1792#12))
  | 1050 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid0Instr (i : Fin 11) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨1040 + i.val, by omega⟩) =
      some (commitMid0Instr (1040 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 1040 ≤ idx) (hhi : idx < 1051)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  have h := decode_commitMid0Instr ⟨idx - 1040, by omega⟩
  have heq : 1040 + (idx - 1040) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1AInstr : Nat → Instruction
  | 1819 => .base (.BNE .x10 .x19 (5120#13))
  | 1820 => .base (.ADDI .x10 .x8 (4000#12))
  | 1821 => .base (.ADDI .x12 .x18 (4064#12))
  | 1822 => .base (.ADDI .x6 .x0 (1023#12))
  | 1823 => .base (.SLLI .x6 .x6 (11#6))
  | 1824 => .base (.ADDI .x6 .x6 (2047#12))
  | 1825 => .base (.SLLI .x6 .x6 (11#6))
  | 1826 => .base (.ADDI .x6 .x6 (1952#12))
  | 1827 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1AInstr (i : Fin 9) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨1819 + i.val, by omega⟩) =
      some (commitMid1AInstr (1819 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 1819 ≤ idx) (hhi : idx < 1828)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  have h := decode_commitMid1AInstr ⟨idx - 1819, by omega⟩
  have heq : 1819 + (idx - 1819) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1BInstr : Nat → Instruction
  | 2596 => .base (.BNE .x10 .x19 (5120#13))
  | 2597 => .base (.ADDI .x10 .x18 (4000#12))
  | 2598 => .base (.ADDI .x12 .x9 (4064#12))
  | 2599 => .base (.ADDI .x6 .x0 (367#12))
  | 2600 => .base (.SLLI .x6 .x6 (11#6))
  | 2601 => .base (.ADDI .x6 .x6 (2047#12))
  | 2602 => .base (.SLLI .x6 .x6 (11#6))
  | 2603 => .base (.ADDI .x6 .x6 (1952#12))
  | 2604 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1BInstr (i : Fin 9) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨2596 + i.val, by omega⟩) =
      some (commitMid1BInstr (2596 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 2596 ≤ idx) (hhi : idx < 2605)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  have h := decode_commitMid1BInstr ⟨idx - 2596, by omega⟩
  have heq : 2596 + (idx - 2596) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1CInstr : Nat → Instruction
  | 3373 => .base (.BNE .x10 .x19 (5120#13))
  | 3374 => .base (.ADDI .x10 .x9 (4000#12))
  | 3375 => .base (.ADDI .x6 .x0 (128#12))
  | 3376 => .base (.SLLI .x6 .x6 (11#6))
  | 3377 => .base (.SLLI .x6 .x6 (11#6))
  | 3378 => .base (.ADD .x12 .x9 .x6)
  | 3379 => .base (.ADDI .x12 .x12 (4064#12))
  | 3380 => .base (.ADDI .x19 .x18 (4000#12))
  | _ => .base .EBREAK

private theorem decode_commitMid1CInstr (i : Fin 8) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨3373 + i.val, by omega⟩) =
      some (commitMid1CInstr (3373 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (hlo : 3373 ≤ idx) (hhi : idx < 3381)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  have h := decode_commitMid1CInstr ⟨idx - 3373, by omega⟩
  have heq : 3373 + (idx - 3373) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitTailInstr : Nat → Instruction
  | 4149 => .base (.BNE .x10 .x19 (5120#13))
  | 4150 => .base (.LD .x6 .x12 (0#12))
  | 4151 => .base (.SD .x26 .x6 (0#12))
  | 4152 => .base (.LD .x6 .x12 (8#12))
  | 4153 => .base (.SD .x26 .x6 (8#12))
  | 4154 => .base (.LD .x6 .x12 (16#12))
  | 4155 => .base (.SD .x26 .x6 (16#12))
  | 4156 => .base (.LD .x6 .x12 (24#12))
  | 4157 => .base (.SD .x26 .x6 (24#12))
  | 4158 => .base (.ADDI .x5 .x0 (1#12))
  | 4159 => .base (.ADDI .x10 .x0 (0#12))
  | 4160 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 12) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4149 + i.val, by omega⟩) =
      some (commitTailInstr (4149 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 4149 ≤ idx) (hhi : idx < 4161)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 4149, by omega⟩
  have heq : 4149 + (idx - 4149) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

/-! ### Opening Program (158 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.BEQ .x16 .x0 (616#13))
  | 1 => .base (.ADDI .x8 .x12 (0#12))
  | 2 => .base (.ADDI .x9 .x13 (0#12))
  | 3 => .base (.SLLI .x6 .x16 (3#6))
  | 4 => .base (.ADD .x18 .x9 .x6)
  | 5 => .base (.ADDI .x19 .x15 (0#12))
  | 6 => .base (.ADDI .x20 .x15 (0#12))
  | 7 => .base (.ADDI .x21 .x0 (4#12))
  | 8 => .base (.SLLI .x21 .x21 (11#6))
  | 9 => .base (.SLLI .x21 .x21 (11#6))
  | 10 => .base (.ADDI .x22 .x0 (5#12))
  | 11 => .base (.SLLI .x22 .x22 (11#6))
  | 12 => .base (.ADDI .x22 .x22 (2047#12))
  | 13 => .base (.SLLI .x22 .x22 (11#6))
  | 14 => .base (.ADDI .x22 .x22 (1619#12))
  | 15 => .base (.ADDI .x6 .x0 (192#12))
  | 16 => .base (.SLLI .x6 .x6 (11#6))
  | 17 => .base (.SLLI .x6 .x6 (11#6))
  | 18 => .base (.ADD .x23 .x8 .x6)
  | 19 => .base (.ADDI .x24 .x0 (2#12))
  | 20 => .base (.SLLI .x24 .x24 (11#6))
  | 21 => .base (.ADDI .x25 .x0 (3#12))
  | 22 => .base (.ADDI .x27 .x0 (1#12))
  | 23 => .base (.LD .x14 .x9 (0#12))
  | 24 => .base (.ADDI .x9 .x9 (8#12))
  | 25 => .base (.SRLI .x6 .x14 (1#6))
  | 26 => .base (.SLLI .x7 .x6 (7#6))
  | 27 => .base (.SLLI .x15 .x6 (6#6))
  | 28 => .base (.ADD .x7 .x7 .x15)
  | 29 => .base (.SLLI .x15 .x6 (3#6))
  | 30 => .base (.SUB .x7 .x7 .x15)
  | 31 => .base (.ADD .x7 .x23 .x7)
  | 32 => .base (.ADDI .x7 .x7 (72#12))
  | 33 => .base (.ANDI .x15 .x14 (1#12))
  | 34 => .base (.SLLI .x15 .x15 (4#6))
  | 35 => .base (.ADD .x7 .x7 .x15)
  | 36 => .base (.LD .x28 .x7 (0#12))
  | 37 => .base (.SD .x20 .x28 (0#12))
  | 38 => .base (.LD .x28 .x7 (8#12))
  | 39 => .base (.SD .x20 .x28 (8#12))
  | 40 => .base (.LD .x28 .x7 (16#12))
  | 41 => .base (.SD .x20 .x28 (16#12))
  | 42 => .base (.ADDI .x20 .x20 (24#12))
  | 43 => .base (.DIVU .x6 .x14 .x25)
  | 44 => .base (.SLLI .x7 .x6 (1#6))
  | 45 => .base (.ADD .x7 .x7 .x6)
  | 46 => .base (.SUB .x15 .x14 .x7)
  | 47 => .base (.SLLI .x7 .x7 (5#6))
  | 48 => .base (.ADD .x7 .x8 .x7)
  | 49 => .base (.ADDI .x16 .x7 (0#12))
  | 50 => .base (.ADDI .x17 .x7 (64#12))
  | 51 => .base (.BNE .x15 .x0 (12#13))
  | 52 => .base (.ADDI .x16 .x7 (32#12))
  | 53 => .base (.JAL .x0 (16#21))
  | 54 => .base (.ADDI .x15 .x15 (4095#12))
  | 55 => .base (.BEQ .x15 .x0 (8#13))
  | 56 => .base (.ADDI .x17 .x7 (32#12))
  | 57 => .base (.LD .x28 .x16 (0#12))
  | 58 => .base (.SD .x20 .x28 (0#12))
  | 59 => .base (.LD .x28 .x16 (8#12))
  | 60 => .base (.SD .x20 .x28 (8#12))
  | 61 => .base (.LD .x28 .x16 (16#12))
  | 62 => .base (.SD .x20 .x28 (16#12))
  | 63 => .base (.LD .x28 .x16 (24#12))
  | 64 => .base (.SD .x20 .x28 (24#12))
  | 65 => .base (.LD .x28 .x17 (0#12))
  | 66 => .base (.SD .x20 .x28 (32#12))
  | 67 => .base (.LD .x28 .x17 (8#12))
  | 68 => .base (.SD .x20 .x28 (40#12))
  | 69 => .base (.LD .x28 .x17 (16#12))
  | 70 => .base (.SD .x20 .x28 (48#12))
  | 71 => .base (.LD .x28 .x17 (24#12))
  | 72 => .base (.SD .x20 .x28 (56#12))
  | 73 => .base (.ADDI .x20 .x20 (64#12))
  | 74 => .base (.ADD .x14 .x21 .x6)
  | 75 => .base (.BLTU .x14 .x22 (8064#13))
  | 76 => .base (.SUB .x14 .x14 .x22)
  | 77 => .base (.ADD .x6 .x24 .x14)
  | 78 => .base (.SB .x6 .x27 (0#12))
  | 79 => .base (.BNE .x9 .x18 (7968#13))
  | 80 => .base (.ADDI .x14 .x24 (0#12))
  | 81 => .base (.ADDI .x15 .x24 (286#12))
  | 82 => .base (.ADDI .x16 .x24 (428#12))
  | 83 => .base (.ADDI .x6 .x0 (6#12))
  | 84 => .base (.SLLI .x6 .x6 (11#6))
  | 85 => .base (.ADDI .x6 .x6 (1440#12))
  | 86 => .base (.SUB .x17 .x23 .x6)
  | 87 => .base (.LBU .x6 .x14 (0#12))
  | 88 => .base (.LBU .x7 .x14 (1#12))
  | 89 => .base (.LBU .x28 .x14 (2#12))
  | 90 => .base (.OR .x29 .x6 .x7)
  | 91 => .base (.OR .x29 .x29 .x28)
  | 92 => .base (.BEQ .x29 .x0 (128#13))
  | 93 => .base (.SB .x15 .x27 (0#12))
  | 94 => .base (.BNE .x6 .x0 (40#13))
  | 95 => .base (.LD .x30 .x17 (0#12))
  | 96 => .base (.SD .x20 .x30 (0#12))
  | 97 => .base (.LD .x30 .x17 (8#12))
  | 98 => .base (.SD .x20 .x30 (8#12))
  | 99 => .base (.LD .x30 .x17 (16#12))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.SD .x20 .x30 (16#12))
  | 1 => .base (.LD .x30 .x17 (24#12))
  | 2 => .base (.SD .x20 .x30 (24#12))
  | 3 => .base (.ADDI .x20 .x20 (32#12))
  | 4 => .base (.BNE .x7 .x0 (40#13))
  | 5 => .base (.LD .x30 .x17 (32#12))
  | 6 => .base (.SD .x20 .x30 (0#12))
  | 7 => .base (.LD .x30 .x17 (40#12))
  | 8 => .base (.SD .x20 .x30 (8#12))
  | 9 => .base (.LD .x30 .x17 (48#12))
  | 10 => .base (.SD .x20 .x30 (16#12))
  | 11 => .base (.LD .x30 .x17 (56#12))
  | 12 => .base (.SD .x20 .x30 (24#12))
  | 13 => .base (.ADDI .x20 .x20 (32#12))
  | 14 => .base (.BNE .x28 .x0 (40#13))
  | 15 => .base (.LD .x30 .x17 (64#12))
  | 16 => .base (.SD .x20 .x30 (0#12))
  | 17 => .base (.LD .x30 .x17 (72#12))
  | 18 => .base (.SD .x20 .x30 (8#12))
  | 19 => .base (.LD .x30 .x17 (80#12))
  | 20 => .base (.SD .x20 .x30 (16#12))
  | 21 => .base (.LD .x30 .x17 (88#12))
  | 22 => .base (.SD .x20 .x30 (24#12))
  | 23 => .base (.ADDI .x20 .x20 (32#12))
  | 24 => .base (.ADDI .x14 .x14 (3#12))
  | 25 => .base (.ADDI .x15 .x15 (1#12))
  | 26 => .base (.ADDI .x17 .x17 (96#12))
  | 27 => .base (.BNE .x15 .x16 (8032#13))
  | 28 => .base (.LBU .x6 .x14 (0#12))
  | 29 => .base (.BNE .x6 .x0 (40#13))
  | 30 => .base (.LD .x30 .x17 (0#12))
  | 31 => .base (.SD .x20 .x30 (0#12))
  | 32 => .base (.LD .x30 .x17 (8#12))
  | 33 => .base (.SD .x20 .x30 (8#12))
  | 34 => .base (.LD .x30 .x17 (16#12))
  | 35 => .base (.SD .x20 .x30 (16#12))
  | 36 => .base (.LD .x30 .x17 (24#12))
  | 37 => .base (.SD .x20 .x30 (24#12))
  | 38 => .base (.ADDI .x20 .x20 (32#12))
  | 39 => .base (.LBU .x7 .x14 (1#12))
  | 40 => .base (.BNE .x7 .x0 (40#13))
  | 41 => .base (.LD .x30 .x17 (32#12))
  | 42 => .base (.SD .x20 .x30 (0#12))
  | 43 => .base (.LD .x30 .x17 (40#12))
  | 44 => .base (.SD .x20 .x30 (8#12))
  | 45 => .base (.LD .x30 .x17 (48#12))
  | 46 => .base (.SD .x20 .x30 (16#12))
  | 47 => .base (.LD .x30 .x17 (56#12))
  | 48 => .base (.SD .x20 .x30 (24#12))
  | 49 => .base (.ADDI .x20 .x20 (32#12))
  | 50 => .base (.SUB .x11 .x20 .x19)
  | 51 => .base (.ADDI .x5 .x0 (1#12))
  | 52 => .base (.ADDI .x10 .x0 (0#12))
  | 53 => .base .ECALL
  | 54 => .base (.ADDI .x11 .x0 (0#12))
  | 55 => .base (.ADDI .x5 .x0 (1#12))
  | 56 => .base (.ADDI .x10 .x0 (0#12))
  | 57 => .base .ECALL
  | _ => .base .EBREAK

def openingInstr (idx : Nat) : Instruction :=
  if idx < 100 then openingInstr0 idx
  else openingInstr1 (idx - 100)

private theorem decode_opening_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr i.val) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 58) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (openingInstr (100 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 158)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .opening) state = some (openingInstr idx) := by
  apply fetch_of_packed MoonArtifact.openingCode _ state idx hhi hpc
  by_cases h0 : idx < 100
  · exact decode_opening_0 ⟨idx, h0⟩
  ·
    have h := decode_opening_1 ⟨idx - 100, by omega⟩
    have heq : 100 + (idx - 100) = idx := by omega
    simpa only [heq] using h

/-! ### Check Program (269 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.BNE .x16 .x0 (20#13))
  | 1 => .base (.BNE .x17 .x0 (1060#13))
  | 2 => .base (.ADDI .x5 .x0 (1#12))
  | 3 => .base (.ADDI .x10 .x0 (0#12))
  | 4 => .base .ECALL
  | 5 => .base (.ADDI .x8 .x11 (0#12))
  | 6 => .base (.ADDI .x9 .x13 (0#12))
  | 7 => .base (.SLLI .x6 .x16 (3#6))
  | 8 => .base (.ADD .x18 .x9 .x6)
  | 9 => .base (.ADDI .x19 .x14 (0#12))
  | 10 => .base (.ADDI .x20 .x15 (0#12))
  | 11 => .base (.ADD .x21 .x15 .x17)
  | 12 => .base (.ADDI .x22 .x0 (4#12))
  | 13 => .base (.SLLI .x22 .x22 (11#6))
  | 14 => .base (.SLLI .x22 .x22 (11#6))
  | 15 => .base (.ADDI .x23 .x0 (5#12))
  | 16 => .base (.SLLI .x23 .x23 (11#6))
  | 17 => .base (.ADDI .x23 .x23 (2047#12))
  | 18 => .base (.SLLI .x23 .x23 (11#6))
  | 19 => .base (.ADDI .x23 .x23 (1619#12))
  | 20 => .base (.ADDI .x24 .x0 (2#12))
  | 21 => .base (.SLLI .x24 .x24 (11#6))
  | 22 => .base (.ADDI .x25 .x0 (4#12))
  | 23 => .base (.SLLI .x25 .x25 (11#6))
  | 24 => .base (.ADDI .x26 .x0 (256#12))
  | 25 => .base (.ADDI .x27 .x0 (3#12))
  | 26 => .base (.ADDI .x5 .x0 (0#12))
  | 27 => .base (.ADDI .x11 .x0 (96#12))
  | 28 => .base (.ADDI .x13 .x0 (0#12))
  | 29 => .base (.LD .x28 .x9 (0#12))
  | 30 => .base (.ADDI .x9 .x9 (8#12))
  | 31 => .base (.SUB .x6 .x21 .x20)
  | 32 => .base (.ADDI .x7 .x0 (24#12))
  | 33 => .base (.BLTU .x6 .x7 (932#13))
  | 34 => .base (.ADDI .x10 .x19 (0#12))
  | 35 => .base (.ADDI .x12 .x26 (0#12))
  | 36 => .base .ECALL
  | 37 => .base (.LD .x29 .x19 (96#12))
  | 38 => .base (.SD .x26 .x29 (32#12))
  | 39 => .base (.LD .x29 .x19 (104#12))
  | 40 => .base (.SD .x26 .x29 (40#12))
  | 41 => .base (.LD .x29 .x19 (112#12))
  | 42 => .base (.SD .x26 .x29 (48#12))
  | 43 => .base (.LD .x29 .x19 (120#12))
  | 44 => .base (.SD .x26 .x29 (56#12))
  | 45 => .base (.LD .x29 .x19 (128#12))
  | 46 => .base (.SD .x26 .x29 (64#12))
  | 47 => .base (.LD .x29 .x19 (136#12))
  | 48 => .base (.SD .x26 .x29 (72#12))
  | 49 => .base (.LD .x29 .x19 (144#12))
  | 50 => .base (.SD .x26 .x29 (80#12))
  | 51 => .base (.LD .x29 .x19 (152#12))
  | 52 => .base (.SD .x26 .x29 (88#12))
  | 53 => .base (.ANDI .x6 .x28 (1#12))
  | 54 => .base (.SLLI .x7 .x6 (5#6))
  | 55 => .base (.ADDI .x12 .x26 (96#12))
  | 56 => .base (.ADD .x12 .x12 .x7)
  | 57 => .base (.ADDI .x10 .x26 (0#12))
  | 58 => .base .ECALL
  | 59 => .base (.ADDI .x10 .x19 (160#12))
  | 60 => .base (.ADDI .x12 .x12 (32#12))
  | 61 => .base .ECALL
  | 62 => .base (.ADDI .x19 .x19 (256#12))
  | 63 => .base (.BNE .x6 .x0 (16#13))
  | 64 => .base (.SD .x26 .x0 (160#12))
  | 65 => .base (.ADDI .x16 .x26 (168#12))
  | 66 => .base (.JAL .x0 (12#21))
  | 67 => .base (.SD .x26 .x0 (120#12))
  | 68 => .base (.ADDI .x16 .x26 (96#12))
  | 69 => .base (.LD .x29 .x20 (0#12))
  | 70 => .base (.SD .x16 .x29 (0#12))
  | 71 => .base (.LD .x29 .x20 (8#12))
  | 72 => .base (.SD .x16 .x29 (8#12))
  | 73 => .base (.LD .x29 .x20 (16#12))
  | 74 => .base (.SD .x16 .x29 (16#12))
  | 75 => .base (.ADDI .x20 .x20 (24#12))
  | 76 => .base (.ADDI .x10 .x26 (96#12))
  | 77 => .base (.ADDI .x12 .x26 (192#12))
  | 78 => .base .ECALL
  | 79 => .base (.SUB .x6 .x21 .x20)
  | 80 => .base (.ADDI .x7 .x0 (64#12))
  | 81 => .base (.BLTU .x6 .x7 (740#13))
  | 82 => .base (.DIVU .x6 .x28 .x27)
  | 83 => .base (.SLLI .x7 .x6 (1#6))
  | 84 => .base (.ADD .x7 .x7 .x6)
  | 85 => .base (.SUB .x7 .x28 .x7)
  | 86 => .base (.ADDI .x16 .x26 (0#12))
  | 87 => .base (.ADDI .x17 .x26 (64#12))
  | 88 => .base (.SLLI .x15 .x7 (5#6))
  | 89 => .base (.ADD .x15 .x26 .x15)
  | 90 => .base (.BNE .x7 .x0 (12#13))
  | 91 => .base (.ADDI .x16 .x26 (32#12))
  | 92 => .base (.JAL .x0 (16#21))
  | 93 => .base (.ADDI .x7 .x7 (4095#12))
  | 94 => .base (.BEQ .x7 .x0 (8#13))
  | 95 => .base (.ADDI .x17 .x26 (32#12))
  | 96 => .base (.LD .x29 .x26 (192#12))
  | 97 => .base (.SD .x15 .x29 (0#12))
  | 98 => .base (.LD .x29 .x26 (200#12))
  | 99 => .base (.SD .x15 .x29 (8#12))
  | _ => .base .EBREAK

private def checkInstr1 : Nat → Instruction
  | 0 => .base (.LD .x29 .x26 (208#12))
  | 1 => .base (.SD .x15 .x29 (16#12))
  | 2 => .base (.LD .x29 .x26 (216#12))
  | 3 => .base (.SD .x15 .x29 (24#12))
  | 4 => .base (.LD .x29 .x20 (0#12))
  | 5 => .base (.SD .x16 .x29 (0#12))
  | 6 => .base (.LD .x29 .x20 (8#12))
  | 7 => .base (.SD .x16 .x29 (8#12))
  | 8 => .base (.LD .x29 .x20 (16#12))
  | 9 => .base (.SD .x16 .x29 (16#12))
  | 10 => .base (.LD .x29 .x20 (24#12))
  | 11 => .base (.SD .x16 .x29 (24#12))
  | 12 => .base (.LD .x29 .x20 (32#12))
  | 13 => .base (.SD .x17 .x29 (0#12))
  | 14 => .base (.LD .x29 .x20 (40#12))
  | 15 => .base (.SD .x17 .x29 (8#12))
  | 16 => .base (.LD .x29 .x20 (48#12))
  | 17 => .base (.SD .x17 .x29 (16#12))
  | 18 => .base (.LD .x29 .x20 (56#12))
  | 19 => .base (.SD .x17 .x29 (24#12))
  | 20 => .base (.ADDI .x20 .x20 (64#12))
  | 21 => .base (.ADDI .x10 .x26 (0#12))
  | 22 => .base (.ADDI .x12 .x26 (192#12))
  | 23 => .base .ECALL
  | 24 => .base (.ADD .x28 .x22 .x6)
  | 25 => .base (.BLTU .x28 .x23 (8008#13))
  | 26 => .base (.SUB .x28 .x28 .x23)
  | 27 => .base (.ADD .x6 .x24 .x28)
  | 28 => .base (.SLLI .x7 .x28 (5#6))
  | 29 => .base (.ADD .x7 .x25 .x7)
  | 30 => .base (.LBU .x15 .x6 (0#12))
  | 31 => .base (.BNE .x15 .x0 (48#13))
  | 32 => .base (.ADDI .x15 .x0 (1#12))
  | 33 => .base (.SB .x6 .x15 (0#12))
  | 34 => .base (.LD .x29 .x26 (192#12))
  | 35 => .base (.SD .x7 .x29 (0#12))
  | 36 => .base (.LD .x29 .x26 (200#12))
  | 37 => .base (.SD .x7 .x29 (8#12))
  | 38 => .base (.LD .x29 .x26 (208#12))
  | 39 => .base (.SD .x7 .x29 (16#12))
  | 40 => .base (.LD .x29 .x26 (216#12))
  | 41 => .base (.SD .x7 .x29 (24#12))
  | 42 => .base (.JAL .x0 (52#21))
  | 43 => .base (.LD .x29 .x26 (192#12))
  | 44 => .base (.LD .x30 .x7 (0#12))
  | 45 => .base (.BNE .x29 .x30 (484#13))
  | 46 => .base (.LD .x29 .x26 (200#12))
  | 47 => .base (.LD .x30 .x7 (8#12))
  | 48 => .base (.BNE .x29 .x30 (472#13))
  | 49 => .base (.LD .x29 .x26 (208#12))
  | 50 => .base (.LD .x30 .x7 (16#12))
  | 51 => .base (.BNE .x29 .x30 (460#13))
  | 52 => .base (.LD .x29 .x26 (216#12))
  | 53 => .base (.LD .x30 .x7 (24#12))
  | 54 => .base (.BNE .x29 .x30 (448#13))
  | 55 => .base (.BNE .x9 .x18 (7688#13))
  | 56 => .base (.ADDI .x14 .x24 (0#12))
  | 57 => .base (.ADDI .x15 .x24 (286#12))
  | 58 => .base (.ADDI .x16 .x24 (428#12))
  | 59 => .base (.ADDI .x17 .x25 (0#12))
  | 60 => .base (.ADDI .x6 .x0 (4#12))
  | 61 => .base (.SLLI .x6 .x6 (11#6))
  | 62 => .base (.ADDI .x6 .x6 (960#12))
  | 63 => .base (.ADD .x28 .x25 .x6)
  | 64 => .base (.LBU .x6 .x14 (0#12))
  | 65 => .base (.LBU .x7 .x14 (1#12))
  | 66 => .base (.LBU .x29 .x14 (2#12))
  | 67 => .base (.OR .x30 .x6 .x7)
  | 68 => .base (.OR .x30 .x30 .x29)
  | 69 => .base (.BEQ .x30 .x0 (180#13))
  | 70 => .base (.ADDI .x30 .x0 (1#12))
  | 71 => .base (.SB .x15 .x30 (0#12))
  | 72 => .base (.BNE .x6 .x0 (52#13))
  | 73 => .base (.SUB .x30 .x21 .x20)
  | 74 => .base (.ADDI .x31 .x0 (32#12))
  | 75 => .base (.BLTU .x30 .x31 (364#13))
  | 76 => .base (.LD .x30 .x20 (0#12))
  | 77 => .base (.SD .x17 .x30 (0#12))
  | 78 => .base (.LD .x30 .x20 (8#12))
  | 79 => .base (.SD .x17 .x30 (8#12))
  | 80 => .base (.LD .x30 .x20 (16#12))
  | 81 => .base (.SD .x17 .x30 (16#12))
  | 82 => .base (.LD .x30 .x20 (24#12))
  | 83 => .base (.SD .x17 .x30 (24#12))
  | 84 => .base (.ADDI .x20 .x20 (32#12))
  | 85 => .base (.BNE .x7 .x0 (52#13))
  | 86 => .base (.SUB .x30 .x21 .x20)
  | 87 => .base (.ADDI .x31 .x0 (32#12))
  | 88 => .base (.BLTU .x30 .x31 (312#13))
  | 89 => .base (.LD .x30 .x20 (0#12))
  | 90 => .base (.SD .x17 .x30 (32#12))
  | 91 => .base (.LD .x30 .x20 (8#12))
  | 92 => .base (.SD .x17 .x30 (40#12))
  | 93 => .base (.LD .x30 .x20 (16#12))
  | 94 => .base (.SD .x17 .x30 (48#12))
  | 95 => .base (.LD .x30 .x20 (24#12))
  | 96 => .base (.SD .x17 .x30 (56#12))
  | 97 => .base (.ADDI .x20 .x20 (32#12))
  | 98 => .base (.BNE .x29 .x0 (52#13))
  | 99 => .base (.SUB .x30 .x21 .x20)
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.ADDI .x31 .x0 (32#12))
  | 1 => .base (.BLTU .x30 .x31 (260#13))
  | 2 => .base (.LD .x30 .x20 (0#12))
  | 3 => .base (.SD .x17 .x30 (64#12))
  | 4 => .base (.LD .x30 .x20 (8#12))
  | 5 => .base (.SD .x17 .x30 (72#12))
  | 6 => .base (.LD .x30 .x20 (16#12))
  | 7 => .base (.SD .x17 .x30 (80#12))
  | 8 => .base (.LD .x30 .x20 (24#12))
  | 9 => .base (.SD .x17 .x30 (88#12))
  | 10 => .base (.ADDI .x20 .x20 (32#12))
  | 11 => .base (.ADDI .x10 .x17 (0#12))
  | 12 => .base (.ADDI .x12 .x28 (0#12))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x14 .x14 (3#12))
  | 15 => .base (.ADDI .x15 .x15 (1#12))
  | 16 => .base (.ADDI .x17 .x17 (96#12))
  | 17 => .base (.ADDI .x28 .x28 (32#12))
  | 18 => .base (.BNE .x15 .x16 (7976#13))
  | 19 => .base (.LBU .x6 .x14 (0#12))
  | 20 => .base (.BNE .x6 .x0 (52#13))
  | 21 => .base (.SUB .x30 .x21 .x20)
  | 22 => .base (.ADDI .x31 .x0 (32#12))
  | 23 => .base (.BLTU .x30 .x31 (172#13))
  | 24 => .base (.LD .x30 .x20 (0#12))
  | 25 => .base (.SD .x17 .x30 (0#12))
  | 26 => .base (.LD .x30 .x20 (8#12))
  | 27 => .base (.SD .x17 .x30 (8#12))
  | 28 => .base (.LD .x30 .x20 (16#12))
  | 29 => .base (.SD .x17 .x30 (16#12))
  | 30 => .base (.LD .x30 .x20 (24#12))
  | 31 => .base (.SD .x17 .x30 (24#12))
  | 32 => .base (.ADDI .x20 .x20 (32#12))
  | 33 => .base (.LBU .x7 .x14 (1#12))
  | 34 => .base (.BNE .x7 .x0 (52#13))
  | 35 => .base (.SUB .x30 .x21 .x20)
  | 36 => .base (.ADDI .x31 .x0 (32#12))
  | 37 => .base (.BLTU .x30 .x31 (116#13))
  | 38 => .base (.LD .x30 .x20 (0#12))
  | 39 => .base (.SD .x17 .x30 (32#12))
  | 40 => .base (.LD .x30 .x20 (8#12))
  | 41 => .base (.SD .x17 .x30 (40#12))
  | 42 => .base (.LD .x30 .x20 (16#12))
  | 43 => .base (.SD .x17 .x30 (48#12))
  | 44 => .base (.LD .x30 .x20 (24#12))
  | 45 => .base (.SD .x17 .x30 (56#12))
  | 46 => .base (.ADDI .x20 .x20 (32#12))
  | 47 => .base (.ADDI .x10 .x17 (0#12))
  | 48 => .base (.ADDI .x12 .x28 (0#12))
  | 49 => .base .ECALL
  | 50 => .base (.BNE .x20 .x21 (64#13))
  | 51 => .base (.LD .x29 .x28 (0#12))
  | 52 => .base (.LD .x30 .x8 (0#12))
  | 53 => .base (.BNE .x29 .x30 (52#13))
  | 54 => .base (.LD .x29 .x28 (8#12))
  | 55 => .base (.LD .x30 .x8 (8#12))
  | 56 => .base (.BNE .x29 .x30 (40#13))
  | 57 => .base (.LD .x29 .x28 (16#12))
  | 58 => .base (.LD .x30 .x8 (16#12))
  | 59 => .base (.BNE .x29 .x30 (28#13))
  | 60 => .base (.LD .x29 .x28 (24#12))
  | 61 => .base (.LD .x30 .x8 (24#12))
  | 62 => .base (.BNE .x29 .x30 (16#13))
  | 63 => .base (.ADDI .x5 .x0 (1#12))
  | 64 => .base (.ADDI .x10 .x0 (0#12))
  | 65 => .base .ECALL
  | 66 => .base (.ADDI .x5 .x0 (1#12))
  | 67 => .base (.ADDI .x10 .x0 (1#12))
  | 68 => .base .ECALL
  | _ => .base .EBREAK

def checkInstr (idx : Nat) : Instruction :=
  if idx < 100 then checkInstr0 idx
  else if idx < 200 then checkInstr1 (idx - 100)
  else checkInstr2 (idx - 200)

private theorem decode_check_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨i.val, by omega⟩) =
      some (checkInstr i.val) := by
  revert i; decide

private theorem decode_check_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (checkInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_check_2 (i : Fin 69) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (checkInstr (200 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 269)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .check) state = some (checkInstr idx) := by
  apply fetch_of_packed MoonArtifact.checkCode _ state idx hhi hpc
  by_cases h0 : idx < 100
  · exact decode_check_0 ⟨idx, h0⟩
  ·
    by_cases h1 : idx < 200
    · have h := decode_check_1 ⟨idx - 100, by omega⟩
      have heq : 100 + (idx - 100) = idx := by omega
      simpa only [heq] using h
    ·
      have h := decode_check_2 ⟨idx - 200, by omega⟩
      have heq : 200 + (idx - 200) = idx := by omega
      simpa only [heq] using h

end CommitGolfCandidate
