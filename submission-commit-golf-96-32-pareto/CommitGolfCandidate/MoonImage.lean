import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨3154116544, 8397000416⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 7449087968, 7583305696, 11878272992⟩ := rfl

theorem commit_dataBase : dataBase (submission.image .commit) = 68719476000 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem opening_dataBase : dataBase (submission.image .opening) = 68719475936 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem check_dataBase : dataBase (submission.image .check) = 68719475936 := by
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

/-! ### Embedded Data Table Verification -/

def packedDword {n : Nat} (p : ArtifactEncoding.Packed n) (off : Nat) (_h : off + 8 ≤ n) : Word :=
  BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (if hj : off + j < n then (p.get 8 ⟨off + j, hj⟩).toNat else 0) * 2 ^ (8 * j))

theorem commitData_dword_0 (i : Fin 23) :
    packedDword MoonArtifact.commitData (32 * i.val) (by omega) =
      BitVec.ofNat 64 (levelBase i.val) := by
  revert i; decide

theorem commitData_dword_1 (i : Fin 23) :
    packedDword MoonArtifact.commitData (32 * i.val + 8) (by omega) =
      BitVec.ofNat 64 (levelBase (i.val + 1)) := by
  revert i; decide

theorem commitData_dword_2 (i : Fin 23) :
    packedDword MoonArtifact.commitData (32 * i.val + 16) (by omega) =
      BitVec.ofNat 64 (levelSize (i.val + 1) / 2) := by
  revert i; decide

theorem commitData_dword_3 (i : Fin 23) :
    packedDword MoonArtifact.commitData (32 * i.val + 24) (by omega) = 0#64 := by
  revert i; decide

theorem openingData_dword_0 (l : Fin 25) :
    packedDword MoonArtifact.openingData (32 * l.val) (by omega) =
      BitVec.ofNat 64 (levelBase l.val) := by
  revert l; decide

theorem openingData_dword_1 (l : Fin 25) :
    packedDword MoonArtifact.openingData (32 * l.val + 8) (by omega) =
      BitVec.ofNat 64 (levelSize l.val) := by
  revert l; decide

theorem openingData_dword_2 (l : Fin 25) :
    packedDword MoonArtifact.openingData (32 * l.val + 16) (by omega) =
      BitVec.ofNat 64 (capMarkOff l.val) := by
  revert l; decide

theorem openingData_dword_3 (l : Fin 25) :
    packedDword MoonArtifact.openingData (32 * l.val + 24) (by omega) =
      BitVec.ofNat 64 (capValOff l.val) := by
  revert l; decide

theorem checkData_eq_openingData : MoonArtifact.checkData = MoonArtifact.openingData := rfl

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

def randWord : Nat → BitVec 32
  | 0 => 0x00000073#32
  | 1 => 0x0b850513#32
  | _ => 0#32

def randInstr : Nat → Instruction
  | 0 => .base .ECALL
  | 1 => .base (.ADDI .x10 .x10 (184#12))
  | _ => .base .EBREAK

theorem decode_randWord (j : Fin 2) :
    decodeInstruction (randWord j.val) = some (randInstr j.val) := by
  revert j; decide

private theorem commit_fetch_rand_words_0 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨14 + 2 * (0 + k.val) + j.val, by omega⟩ = randWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_1 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨14 + 2 * (128 + k.val) + j.val, by omega⟩ = randWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_2 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨14 + 2 * (256 + k.val) + j.val, by omega⟩ = randWord j.val := by
  revert k j; decide

private theorem commit_fetch_rand_words_3 (k : Fin 128) (j : Fin 2) :
    MoonArtifact.commitCode.get 32 ⟨14 + 2 * (384 + k.val) + j.val, by omega⟩ = randWord j.val := by
  revert k j; decide

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 512) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (14 + 2 * k + j) (by omega)
    (randWord j) hpc _ (randInstr j) (decode_randWord ⟨j, hj⟩)
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
    MoonArtifact.commitCode.get 32 ⟨1047 + 3 * (0 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

private theorem commit_fetch_leaf0_words_1 (k : Fin 128) (j : Fin 3) :
    MoonArtifact.commitCode.get 32 ⟨1047 + 3 * (128 + k.val) + j.val, by omega⟩ = leaf0Word j.val := by
  revert k j; decide

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 256) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1047 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (1047 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  by_cases h0 : k < 128
  · simpa using commit_fetch_leaf0_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf0_words_1 ⟨k - 128, by omega⟩ ⟨j, hj⟩
    simpa [show 128 + (k - 128) = k by omega] using this

def leaf12Word : Nat → BitVec 32
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

def leaf12Instr : Nat → Instruction
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

theorem decode_leaf12Word (j : Fin 12) :
    decodeInstruction (leaf12Word j.val) = some (leaf12Instr j.val) := by
  revert j; decide

private theorem commit_fetch_leaf12_words_0 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨1822 + 12 * (0 + k.val) + j.val, by omega⟩ = leaf12Word j.val := by
  revert k j; decide

private theorem commit_fetch_leaf12_words_1 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨1822 + 12 * (32 + k.val) + j.val, by omega⟩ = leaf12Word j.val := by
  revert k j; decide

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (1822 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (1822 + 12 * k + j) (by omega)
    (leaf12Word j) hpc _ (leaf12Instr j) (decode_leaf12Word ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_leaf12_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf12_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

def leaf3Word : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x00061f23#32
  | 4 => 0x05850513#32
  | 5 => 0x02060613#32
  | 6 => 0x00000073#32
  | 7 => 0x00061f23#32
  | _ => 0#32

def leaf3Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.SH .x12 .x0 (30#12))
  | 4 => .base (.ADDI .x10 .x10 (88#12))
  | 5 => .base (.ADDI .x12 .x12 (32#12))
  | 6 => .base .ECALL
  | 7 => .base (.SH .x12 .x0 (30#12))
  | _ => .base .EBREAK

theorem decode_leaf3Word (j : Fin 8) :
    decodeInstruction (leaf3Word j.val) = some (leaf3Instr j.val) := by
  revert j; decide

private theorem commit_fetch_leaf3_words_0 (k : Fin 64) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨2597 + 8 * (0 + k.val) + j.val, by omega⟩ = leaf3Word j.val := by
  revert k j; decide

private theorem commit_fetch_leaf3_words_1 (k : Fin 64) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨2597 + 8 * (64 + k.val) + j.val, by omega⟩ = leaf3Word j.val := by
  revert k j; decide

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (2597 + 8 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (2597 + 8 * k + j) (by omega)
    (leaf3Word j) hpc _ (leaf3Instr j) (decode_leaf3Word ⟨j, hj⟩)
  by_cases h0 : k < 64
  · simpa using commit_fetch_leaf3_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_leaf3_words_1 ⟨k - 64, by omega⟩ ⟨j, hj⟩
    simpa [show 64 + (k - 64) = k by omega] using this

def bin240Word : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x00061f23#32
  | 4 => 0x06050513#32
  | 5 => 0x02060613#32
  | 6 => 0x00000073#32
  | 7 => 0x00061f23#32
  | _ => 0#32

def bin240Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.SH .x12 .x0 (30#12))
  | 4 => .base (.ADDI .x10 .x10 (96#12))
  | 5 => .base (.ADDI .x12 .x12 (32#12))
  | 6 => .base .ECALL
  | 7 => .base (.SH .x12 .x0 (30#12))
  | _ => .base .EBREAK

theorem decode_bin240Word (j : Fin 8) :
    decodeInstruction (bin240Word j.val) = some (bin240Instr j.val) := by
  revert j; decide

private theorem commit_fetch_bin240_words_0 (k : Fin 32) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨3637 + 8 * (0 + k.val) + j.val, by omega⟩ = bin240Word j.val := by
  revert k j; decide

private theorem commit_fetch_bin240_words_1 (k : Fin 32) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨3637 + 8 * (32 + k.val) + j.val, by omega⟩ = bin240Word j.val := by
  revert k j; decide

theorem commit_fetch_bin240 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (3637 + 8 * k + j))) :
    fetch (submission.image .commit) state = some (bin240Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (3637 + 8 * k + j) (by omega)
    (bin240Word j) hpc _ (bin240Instr j) (decode_bin240Word ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_bin240_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_bin240_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

def bin238Word : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x01863303#32
  | 4 => 0x01b37333#32
  | 5 => 0x00663c23#32
  | 6 => 0x06050513#32
  | 7 => 0x02060613#32
  | 8 => 0x00000073#32
  | 9 => 0x01863303#32
  | 10 => 0x01b37333#32
  | 11 => 0x00663c23#32
  | _ => 0#32

def bin238Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.LD .x6 .x12 (24#12))
  | 4 => .base (.AND .x6 .x6 .x27)
  | 5 => .base (.SD .x12 .x6 (24#12))
  | 6 => .base (.ADDI .x10 .x10 (96#12))
  | 7 => .base (.ADDI .x12 .x12 (32#12))
  | 8 => .base .ECALL
  | 9 => .base (.LD .x6 .x12 (24#12))
  | 10 => .base (.AND .x6 .x6 .x27)
  | 11 => .base (.SD .x12 .x6 (24#12))
  | _ => .base .EBREAK

theorem decode_bin238Word (j : Fin 12) :
    decodeInstruction (bin238Word j.val) = some (bin238Instr j.val) := by
  revert j; decide

private theorem commit_fetch_bin238_words_0 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨4181 + 12 * (0 + k.val) + j.val, by omega⟩ = bin238Word j.val := by
  revert k j; decide

private theorem commit_fetch_bin238_words_1 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨4181 + 12 * (32 + k.val) + j.val, by omega⟩ = bin238Word j.val := by
  revert k j; decide

theorem commit_fetch_bin238 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4181 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (bin238Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (4181 + 12 * k + j) (by omega)
    (bin238Word j) hpc _ (bin238Instr j) (decode_bin238Word ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_bin238_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_bin238_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (1536#12))
  | 4 => .base (.SLLI .x6 .x6 (20#6))
  | 5 => .base (.ADDI .x6 .x6 (4032#12))
  | 6 => .base (.ADD .x18 .x9 .x6)
  | 7 => .base (.ADDI .x5 .x0 (2#12))
  | 8 => .base (.ADDI .x10 .x18 (72#12))
  | 9 => .base (.ADDI .x11 .x0 (40#12))
  | 10 => .base (.ADDI .x6 .x0 (1472#12))
  | 11 => .base (.SLLI .x6 .x6 (20#6))
  | 12 => .base (.ADDI .x6 .x6 (72#12))
  | 13 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr (i : Fin 14) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 14)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  have h := decode_commitPrefixInstr ⟨idx - 0, by omega⟩
  have heq : 0 + (idx - 0) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid0Instr : Nat → Instruction
  | 1038 => .base (.BNE .x10 .x19 (4096#13))
  | 1039 => .base (.ADDI .x5 .x0 (0#12))
  | 1040 => .base (.ADDI .x11 .x0 (96#12))
  | 1041 => .base (.ADDI .x13 .x0 (0#12))
  | 1042 => .base (.ADDI .x10 .x8 (3840#12))
  | 1043 => .base (.ADDI .x6 .x0 (1024#12))
  | 1044 => .base (.SLLI .x6 .x6 (22#6))
  | 1045 => .base (.ADDI .x6 .x6 (3840#12))
  | 1046 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid0Instr (i : Fin 9) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨1038 + i.val, by omega⟩) =
      some (commitMid0Instr (1038 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 1038 ≤ idx) (hhi : idx < 1047)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  have h := decode_commitMid0Instr ⟨idx - 1038, by omega⟩
  have heq : 1038 + (idx - 1038) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1Instr : Nat → Instruction
  | 1815 => .base (.BNE .x10 .x19 (5120#13))
  | 1816 => .base (.ADDI .x10 .x8 (4000#12))
  | 1817 => .base (.ADDI .x12 .x18 (4064#12))
  | 1818 => .base (.ADDI .x6 .x0 (1024#12))
  | 1819 => .base (.SLLI .x6 .x6 (22#6))
  | 1820 => .base (.ADDI .x6 .x6 (4000#12))
  | 1821 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1Instr (i : Fin 7) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨1815 + i.val, by omega⟩) =
      some (commitMid1Instr (1815 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1Instr (state : MachineState) (idx : Nat) (hlo : 1815 ≤ idx) (hhi : idx < 1822)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1Instr idx) := by
  have h := decode_commitMid1Instr ⟨idx - 1815, by omega⟩
  have heq : 1815 + (idx - 1815) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid2Instr : Nat → Instruction
  | 2590 => .base (.BNE .x10 .x19 (5120#13))
  | 2591 => .base (.ADDI .x10 .x18 (4000#12))
  | 2592 => .base (.ADDI .x12 .x9 (4032#12))
  | 2593 => .base (.ADDI .x6 .x0 (1472#12))
  | 2594 => .base (.SLLI .x6 .x6 (20#6))
  | 2595 => .base (.ADDI .x6 .x6 (4000#12))
  | 2596 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid2Instr (i : Fin 7) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨2590 + i.val, by omega⟩) =
      some (commitMid2Instr (2590 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2Instr (state : MachineState) (idx : Nat) (hlo : 2590 ≤ idx) (hhi : idx < 2597)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2Instr idx) := by
  have h := decode_commitMid2Instr ⟨idx - 2590, by omega⟩
  have heq : 2590 + (idx - 2590) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid3Instr : Nat → Instruction
  | 3621 => .base (.BNE .x10 .x19 (4096#13))
  | 3622 => .base (.ADDI .x24 .x2 (0#12))
  | 3623 => .base (.ADDI .x25 .x2 (32#12))
  | 3624 => .base (.LD .x6 .x24 (0#12))
  | 3625 => .base (.ADD .x10 .x9 .x6)
  | 3626 => .base (.ADDI .x10 .x10 (4000#12))
  | 3627 => .base (.LD .x6 .x24 (8#12))
  | 3628 => .base (.ADD .x12 .x9 .x6)
  | 3629 => .base (.ADDI .x12 .x12 (4032#12))
  | 3630 => .base (.LD .x20 .x24 (16#12))
  | 3631 => .base (.SRLI .x22 .x20 (6#6))
  | 3632 => .base (.BEQ .x22 .x0 (2072#13))
  | 3633 => .base (.SLLI .x6 .x22 (12#6))
  | 3634 => .base (.SLLI .x7 .x22 (13#6))
  | 3635 => .base (.ADD .x6 .x6 .x7)
  | 3636 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid3Instr (i : Fin 16) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨3621 + i.val, by omega⟩) =
      some (commitMid3Instr (3621 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid3Instr (state : MachineState) (idx : Nat) (hlo : 3621 ≤ idx) (hhi : idx < 3637)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid3Instr idx) := by
  have h := decode_commitMid3Instr ⟨idx - 3621, by omega⟩
  have heq : 3621 + (idx - 3621) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid4Instr : Nat → Instruction
  | 4149 => .base (.BNE .x10 .x19 (6144#13))
  | 4150 => .base (.ANDI .x22 .x20 (63#12))
  | 4151 => .base (.BEQ .x22 .x0 (44#13))
  | 4152 => .base (.ADDI .x10 .x10 (96#12))
  | 4153 => .base (.ADDI .x12 .x12 (64#12))
  | 4154 => .base .ECALL
  | 4155 => .base (.SH .x12 .x0 (30#12))
  | 4156 => .base (.ADDI .x10 .x10 (96#12))
  | 4157 => .base (.ADDI .x12 .x12 (32#12))
  | 4158 => .base .ECALL
  | 4159 => .base (.SH .x12 .x0 (30#12))
  | 4160 => .base (.ADDI .x22 .x22 (4095#12))
  | 4161 => .base (.BNE .x22 .x0 (8156#13))
  | 4162 => .base (.ADDI .x24 .x24 (32#12))
  | 4163 => .base (.BNE .x24 .x25 (6036#13))
  | 4164 => .base (.ADDI .x27 .x0 (1#12))
  | 4165 => .base (.SLLI .x27 .x27 (46#6))
  | 4166 => .base (.ADDI .x27 .x27 (4095#12))
  | 4167 => .base (.ADDI .x25 .x2 (736#12))
  | 4168 => .base (.LD .x6 .x24 (0#12))
  | 4169 => .base (.ADD .x10 .x9 .x6)
  | 4170 => .base (.ADDI .x10 .x10 (4000#12))
  | 4171 => .base (.LD .x6 .x24 (8#12))
  | 4172 => .base (.ADD .x12 .x9 .x6)
  | 4173 => .base (.ADDI .x12 .x12 (4032#12))
  | 4174 => .base (.LD .x20 .x24 (16#12))
  | 4175 => .base (.SRLI .x22 .x20 (6#6))
  | 4176 => .base (.BEQ .x22 .x0 (3096#13))
  | 4177 => .base (.SLLI .x6 .x22 (12#6))
  | 4178 => .base (.SLLI .x7 .x22 (13#6))
  | 4179 => .base (.ADD .x6 .x6 .x7)
  | 4180 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid4Instr (i : Fin 32) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4149 + i.val, by omega⟩) =
      some (commitMid4Instr (4149 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid4Instr (state : MachineState) (idx : Nat) (hlo : 4149 ≤ idx) (hhi : idx < 4181)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid4Instr idx) := by
  have h := decode_commitMid4Instr ⟨idx - 4149, by omega⟩
  have heq : 4149 + (idx - 4149) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitTailInstr : Nat → Instruction
  | 4949 => .base (.BNE .x10 .x19 (5120#13))
  | 4950 => .base (.ANDI .x22 .x20 (63#12))
  | 4951 => .base (.BEQ .x22 .x0 (60#13))
  | 4952 => .base (.ADDI .x10 .x10 (96#12))
  | 4953 => .base (.ADDI .x12 .x12 (64#12))
  | 4954 => .base .ECALL
  | 4955 => .base (.LD .x6 .x12 (24#12))
  | 4956 => .base (.AND .x6 .x6 .x27)
  | 4957 => .base (.SD .x12 .x6 (24#12))
  | 4958 => .base (.ADDI .x10 .x10 (96#12))
  | 4959 => .base (.ADDI .x12 .x12 (32#12))
  | 4960 => .base .ECALL
  | 4961 => .base (.LD .x6 .x12 (24#12))
  | 4962 => .base (.AND .x6 .x6 .x27)
  | 4963 => .base (.SD .x12 .x6 (24#12))
  | 4964 => .base (.ADDI .x22 .x22 (4095#12))
  | 4965 => .base (.BNE .x22 .x0 (8140#13))
  | 4966 => .base (.ADDI .x24 .x24 (32#12))
  | 4967 => .base (.BNE .x24 .x25 (4996#13))
  | 4968 => .base (.ADDI .x6 .x0 (1536#12))
  | 4969 => .base (.SLLI .x6 .x6 (20#6))
  | 4970 => .base (.ADDI .x6 .x6 (3904#12))
  | 4971 => .base (.ADD .x10 .x9 .x6)
  | 4972 => .base (.ADDI .x6 .x0 (1536#12))
  | 4973 => .base (.SLLI .x6 .x6 (20#6))
  | 4974 => .base (.ADDI .x6 .x6 (4000#12))
  | 4975 => .base (.ADD .x12 .x9 .x6)
  | 4976 => .base .ECALL
  | 4977 => .base (.LD .x6 .x12 (0#12))
  | 4978 => .base (.SD .x26 .x6 (0#12))
  | 4979 => .base (.LD .x6 .x12 (8#12))
  | 4980 => .base (.SD .x26 .x6 (8#12))
  | 4981 => .base (.LD .x6 .x12 (16#12))
  | 4982 => .base (.SD .x26 .x6 (16#12))
  | 4983 => .base (.LD .x6 .x12 (24#12))
  | 4984 => .base (.SD .x26 .x6 (24#12))
  | 4985 => .base (.ADDI .x5 .x0 (1#12))
  | 4986 => .base (.ADDI .x10 .x0 (0#12))
  | 4987 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 39) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4949 + i.val, by omega⟩) =
      some (commitTailInstr (4949 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 4949 ≤ idx) (hhi : idx < 4988)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 4949, by omega⟩
  have heq : 4949 + (idx - 4949) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

/-! ### Opening Program (216 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (432#13))
  | 6 => .base (.ADDI .x12 .x0 (0#12))
  | 7 => .base (.ADDI .x13 .x0 (0#12))
  | 8 => .base (.ADDI .x14 .x0 (63#12))
  | 9 => .base (.ADDI .x31 .x0 (3#12))
  | 10 => .base (.SLLI .x31 .x31 (33#6))
  | 11 => .base (.ADDI .x15 .x31 (0#12))
  | 12 => .base (.ADDI .x16 .x0 (0#12))
  | 13 => .base (.ADDI .x17 .x0 (0#12))
  | 14 => .base (.ADDI .x6 .x0 (1536#12))
  | 15 => .base (.SLLI .x6 .x6 (20#6))
  | 16 => .base (.ADDI .x6 .x6 (8#12))
  | 17 => .base (.ADD .x18 .x9 .x6)
  | 18 => .base (.ADDI .x21 .x0 (2#12))
  | 19 => .base (.SLLI .x21 .x21 (11#6))
  | 20 => .base (.LD .x22 .x24 (0#12))
  | 21 => .base (.SRLI .x6 .x22 (1#6))
  | 22 => .base (.SLLI .x7 .x6 (7#6))
  | 23 => .base (.SLLI .x10 .x6 (6#6))
  | 24 => .base (.ADD .x7 .x7 .x10)
  | 25 => .base (.SLLI .x10 .x6 (3#6))
  | 26 => .base (.SUB .x7 .x7 .x10)
  | 27 => .base (.ANDI .x6 .x22 (1#12))
  | 28 => .base (.SLLI .x6 .x6 (4#6))
  | 29 => .base (.ADD .x7 .x7 .x6)
  | 30 => .base (.ADD .x10 .x18 .x7)
  | 31 => .base (.JAL .x1 (344#21))
  | 32 => .base (.ADDI .x29 .x2 (0#12))
  | 33 => .base (.ADDI .x30 .x2 (64#12))
  | 34 => .base (.XORI .x28 .x22 (1#12))
  | 35 => .base (.SRLI .x6 .x28 (1#6))
  | 36 => .base (.ADD .x28 .x28 .x6)
  | 37 => .base (.SLLI .x28 .x28 (5#6))
  | 38 => .base (.LD .x6 .x29 (0#12))
  | 39 => .base (.ADD .x10 .x9 .x6)
  | 40 => .base (.ADD .x10 .x10 .x28)
  | 41 => .base (.JAL .x1 (384#21))
  | 42 => .base (.SRLI .x22 .x22 (1#6))
  | 43 => .base (.ADDI .x29 .x29 (32#12))
  | 44 => .base (.BNE .x29 .x30 (8152#13))
  | 45 => .base (.ADDI .x30 .x2 (512#12))
  | 46 => .base (.XORI .x28 .x22 (1#12))
  | 47 => .base (.SRLI .x6 .x28 (1#6))
  | 48 => .base (.ADD .x28 .x28 .x6)
  | 49 => .base (.SLLI .x28 .x28 (5#6))
  | 50 => .base (.LD .x6 .x29 (0#12))
  | 51 => .base (.ADD .x10 .x9 .x6)
  | 52 => .base (.ADD .x10 .x10 .x28)
  | 53 => .base (.JAL .x1 (472#21))
  | 54 => .base (.SRLI .x22 .x22 (1#6))
  | 55 => .base (.ADDI .x29 .x29 (32#12))
  | 56 => .base (.BNE .x29 .x30 (8152#13))
  | 57 => .base (.ADD .x6 .x21 .x22)
  | 58 => .base (.ADDI .x7 .x0 (1#12))
  | 59 => .base (.SB .x6 .x7 (0#12))
  | 60 => .base (.ADDI .x24 .x24 (8#12))
  | 61 => .base (.ADDI .x27 .x27 (4095#12))
  | 62 => .base (.BNE .x27 .x0 (8024#13))
  | 63 => .base (.ADDI .x29 .x2 (512#12))
  | 64 => .base (.ADDI .x30 .x2 (768#12))
  | 65 => .base (.LD .x18 .x29 (0#12))
  | 66 => .base (.ADD .x18 .x9 .x18)
  | 67 => .base (.LD .x19 .x29 (8#12))
  | 68 => .base (.LD .x20 .x29 (16#12))
  | 69 => .base (.ADD .x20 .x21 .x20)
  | 70 => .base (.LD .x22 .x29 (48#12))
  | 71 => .base (.ADD .x22 .x21 .x22)
  | 72 => .base (.SRLI .x23 .x19 (1#6))
  | 73 => .base (.ADDI .x24 .x0 (0#12))
  | 74 => .base (.SLLI .x6 .x24 (1#6))
  | 75 => .base (.ADD .x6 .x20 .x6)
  | 76 => .base (.LBU .x7 .x6 (0#12))
  | 77 => .base (.LBU .x8 .x6 (1#12))
  | 78 => .base (.OR .x11 .x7 .x8)
  | 79 => .base (.ADD .x6 .x22 .x24)
  | 80 => .base (.SB .x6 .x11 (0#12))
  | 81 => .base (.BEQ .x7 .x8 (32#13))
  | 82 => .base (.SLLI .x6 .x24 (6#6))
  | 83 => .base (.SLLI .x11 .x24 (5#6))
  | 84 => .base (.ADD .x10 .x6 .x11)
  | 85 => .base (.ADD .x10 .x18 .x10)
  | 86 => .base (.BEQ .x7 .x0 (8#13))
  | 87 => .base (.ADDI .x10 .x10 (32#12))
  | 88 => .base (.JAL .x1 (332#21))
  | 89 => .base (.ADDI .x24 .x24 (1#12))
  | 90 => .base (.BNE .x24 .x23 (8128#13))
  | 91 => .base (.ADDI .x29 .x29 (32#12))
  | 92 => .base (.BNE .x29 .x30 (8084#13))
  | 93 => .base (.ADDI .x10 .x25 (0#12))
  | 94 => .base (.BEQ .x13 .x0 (24#13))
  | 95 => .base (.SB .x10 .x12 (0#12))
  | 96 => .base (.ADDI .x10 .x10 (1#12))
  | 97 => .base (.SRLI .x12 .x12 (8#6))
  | 98 => .base (.ADDI .x13 .x13 (4088#12))
  | 99 => .base (.BNE .x13 .x0 (8176#13))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.BEQ .x17 .x0 (12#13))
  | 1 => .base (.SB .x15 .x16 (0#12))
  | 2 => .base (.ADDI .x15 .x15 (1#12))
  | 3 => .base (.BEQ .x15 .x31 (24#13))
  | 4 => .base (.ADDI .x15 .x15 (4095#12))
  | 5 => .base (.LBU .x6 .x15 (0#12))
  | 6 => .base (.SB .x10 .x6 (0#12))
  | 7 => .base (.ADDI .x10 .x10 (1#12))
  | 8 => .base (.BNE .x15 .x31 (8176#13))
  | 9 => .base (.SUB .x11 .x10 .x26)
  | 10 => .base (.ADDI .x5 .x0 (1#12))
  | 11 => .base (.ADDI .x10 .x0 (0#12))
  | 12 => .base .ECALL
  | 13 => .base (.ADDI .x11 .x0 (0#12))
  | 14 => .base (.ADDI .x5 .x0 (1#12))
  | 15 => .base (.ADDI .x10 .x0 (0#12))
  | 16 => .base .ECALL
  | 17 => .base (.LD .x5 .x10 (0#12))
  | 18 => .base (.SLL .x6 .x5 .x13)
  | 19 => .base (.OR .x12 .x12 .x6)
  | 20 => .base (.SD .x25 .x12 (0#12))
  | 21 => .base (.SRLI .x5 .x5 (1#6))
  | 22 => .base (.SRL .x12 .x5 .x14)
  | 23 => .base (.LD .x5 .x10 (8#12))
  | 24 => .base (.SLL .x6 .x5 .x13)
  | 25 => .base (.OR .x12 .x12 .x6)
  | 26 => .base (.SD .x25 .x12 (8#12))
  | 27 => .base (.SRLI .x5 .x5 (1#6))
  | 28 => .base (.SRL .x12 .x5 .x14)
  | 29 => .base (.LD .x5 .x10 (16#12))
  | 30 => .base (.SLL .x6 .x5 .x13)
  | 31 => .base (.OR .x12 .x12 .x6)
  | 32 => .base (.SD .x25 .x12 (16#12))
  | 33 => .base (.SRLI .x5 .x5 (1#6))
  | 34 => .base (.SRL .x12 .x5 .x14)
  | 35 => .base (.ADDI .x25 .x25 (24#12))
  | 36 => .base (.JALR .x0 .x1 (0#12))
  | 37 => .base (.LD .x5 .x10 (0#12))
  | 38 => .base (.SLL .x6 .x5 .x13)
  | 39 => .base (.OR .x12 .x12 .x6)
  | 40 => .base (.SD .x25 .x12 (0#12))
  | 41 => .base (.SRLI .x5 .x5 (1#6))
  | 42 => .base (.SRL .x12 .x5 .x14)
  | 43 => .base (.LD .x5 .x10 (8#12))
  | 44 => .base (.SLL .x6 .x5 .x13)
  | 45 => .base (.OR .x12 .x12 .x6)
  | 46 => .base (.SD .x25 .x12 (8#12))
  | 47 => .base (.SRLI .x5 .x5 (1#6))
  | 48 => .base (.SRL .x12 .x5 .x14)
  | 49 => .base (.LD .x5 .x10 (16#12))
  | 50 => .base (.SLL .x6 .x5 .x13)
  | 51 => .base (.OR .x12 .x12 .x6)
  | 52 => .base (.SD .x25 .x12 (16#12))
  | 53 => .base (.SRLI .x5 .x5 (1#6))
  | 54 => .base (.SRL .x12 .x5 .x14)
  | 55 => .base (.ADDI .x25 .x25 (24#12))
  | 56 => .base (.LD .x5 .x10 (24#12))
  | 57 => .base (.SLLI .x5 .x5 (16#6))
  | 58 => .base (.SRLI .x5 .x5 (16#6))
  | 59 => .base (.SLL .x6 .x5 .x13)
  | 60 => .base (.OR .x12 .x12 .x6)
  | 61 => .base (.ADDI .x13 .x13 (48#12))
  | 62 => .base (.ADDI .x7 .x0 (64#12))
  | 63 => .base (.BLTU .x13 .x7 (24#13))
  | 64 => .base (.SD .x25 .x12 (0#12))
  | 65 => .base (.ADDI .x25 .x25 (8#12))
  | 66 => .base (.SRLI .x5 .x5 (1#6))
  | 67 => .base (.SRL .x12 .x5 .x14)
  | 68 => .base (.ADDI .x13 .x13 (4032#12))
  | 69 => .base (.XORI .x14 .x13 (63#12))
  | 70 => .base (.JALR .x0 .x1 (0#12))
  | 71 => .base (.LD .x5 .x10 (0#12))
  | 72 => .base (.SLL .x6 .x5 .x13)
  | 73 => .base (.OR .x12 .x12 .x6)
  | 74 => .base (.SD .x25 .x12 (0#12))
  | 75 => .base (.SRLI .x5 .x5 (1#6))
  | 76 => .base (.SRL .x12 .x5 .x14)
  | 77 => .base (.LD .x5 .x10 (8#12))
  | 78 => .base (.SLL .x6 .x5 .x13)
  | 79 => .base (.OR .x12 .x12 .x6)
  | 80 => .base (.SD .x25 .x12 (8#12))
  | 81 => .base (.SRLI .x5 .x5 (1#6))
  | 82 => .base (.SRL .x12 .x5 .x14)
  | 83 => .base (.LD .x5 .x10 (16#12))
  | 84 => .base (.SLL .x6 .x5 .x13)
  | 85 => .base (.OR .x12 .x12 .x6)
  | 86 => .base (.SD .x25 .x12 (16#12))
  | 87 => .base (.SRLI .x5 .x5 (1#6))
  | 88 => .base (.SRL .x12 .x5 .x14)
  | 89 => .base (.ADDI .x25 .x25 (24#12))
  | 90 => .base (.LD .x11 .x10 (24#12))
  | 91 => .base (.SLLI .x5 .x11 (24#6))
  | 92 => .base (.SRLI .x5 .x5 (24#6))
  | 93 => .base (.SLL .x6 .x5 .x13)
  | 94 => .base (.OR .x12 .x12 .x6)
  | 95 => .base (.ADDI .x13 .x13 (40#12))
  | 96 => .base (.ADDI .x7 .x0 (64#12))
  | 97 => .base (.BLTU .x13 .x7 (24#13))
  | 98 => .base (.SD .x25 .x12 (0#12))
  | 99 => .base (.ADDI .x25 .x25 (8#12))
  | _ => .base .EBREAK

private def openingInstr2 : Nat → Instruction
  | 0 => .base (.SRLI .x5 .x5 (1#6))
  | 1 => .base (.SRL .x12 .x5 .x14)
  | 2 => .base (.ADDI .x13 .x13 (4032#12))
  | 3 => .base (.XORI .x14 .x13 (63#12))
  | 4 => .base (.SRLI .x5 .x11 (40#6))
  | 5 => .base (.ANDI .x5 .x5 (63#12))
  | 6 => .base (.SLL .x6 .x5 .x17)
  | 7 => .base (.OR .x16 .x16 .x6)
  | 8 => .base (.ADDI .x17 .x17 (6#12))
  | 9 => .base (.ADDI .x7 .x0 (8#12))
  | 10 => .base (.BLTU .x17 .x7 (20#13))
  | 11 => .base (.SB .x15 .x16 (0#12))
  | 12 => .base (.ADDI .x15 .x15 (1#12))
  | 13 => .base (.SRLI .x16 .x16 (8#6))
  | 14 => .base (.ADDI .x17 .x17 (4088#12))
  | 15 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def openingInstr (idx : Nat) : Instruction :=
  if idx < 100 then openingInstr0 idx
  else if idx < 200 then openingInstr1 (idx - 100)
  else openingInstr2 (idx - 200)

private theorem decode_opening_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr i.val) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (openingInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_opening_2 (i : Fin 16) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (openingInstr (200 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 216)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .opening) state = some (openingInstr idx) := by
  apply fetch_of_packed MoonArtifact.openingCode _ state idx hhi hpc
  by_cases h0 : idx < 100
  · exact decode_opening_0 ⟨idx, h0⟩
  ·
    by_cases h1 : idx < 200
    · have h := decode_opening_1 ⟨idx - 100, by omega⟩
      have heq : 100 + (idx - 100) = idx := by omega
      simpa only [heq] using h
    ·
      have h := decode_opening_2 ⟨idx - 200, by omega⟩
      have heq : 200 + (idx - 200) = idx := by omega
      simpa only [heq] using h

/-! ### Check Program (265 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (896#13))
  | 8 => .base (.JAL .x0 (880#21))
  | 9 => .base (.ADDI .x3 .x0 (0#12))
  | 10 => .base (.ADDI .x4 .x0 (0#12))
  | 11 => .base (.ADDI .x9 .x0 (1#12))
  | 12 => .base (.SLLI .x9 .x9 (46#6))
  | 13 => .base (.ADDI .x9 .x9 (4095#12))
  | 14 => .base (.ADDI .x21 .x0 (256#12))
  | 15 => .base (.ADDI .x18 .x0 (2#12))
  | 16 => .base (.SLLI .x18 .x18 (11#6))
  | 17 => .base (.ADDI .x19 .x0 (4#12))
  | 18 => .base (.SLLI .x19 .x19 (11#6))
  | 19 => .base (.ADDI .x5 .x0 (0#12))
  | 20 => .base (.ADDI .x11 .x0 (96#12))
  | 21 => .base (.ADDI .x13 .x0 (0#12))
  | 22 => .base (.LD .x20 .x24 (0#12))
  | 23 => .base (.ADDI .x6 .x25 (24#12))
  | 24 => .base (.BLTU .x31 .x6 (828#13))
  | 25 => .base (.ADDI .x10 .x8 (0#12))
  | 26 => .base (.ADDI .x12 .x21 (0#12))
  | 27 => .base .ECALL
  | 28 => .base (.LD .x6 .x8 (96#12))
  | 29 => .base (.SD .x21 .x6 (32#12))
  | 30 => .base (.LD .x6 .x8 (104#12))
  | 31 => .base (.SD .x21 .x6 (40#12))
  | 32 => .base (.LD .x6 .x8 (112#12))
  | 33 => .base (.SD .x21 .x6 (48#12))
  | 34 => .base (.LD .x6 .x8 (120#12))
  | 35 => .base (.SD .x21 .x6 (56#12))
  | 36 => .base (.LD .x6 .x8 (128#12))
  | 37 => .base (.SD .x21 .x6 (64#12))
  | 38 => .base (.LD .x6 .x8 (136#12))
  | 39 => .base (.SD .x21 .x6 (72#12))
  | 40 => .base (.LD .x6 .x8 (144#12))
  | 41 => .base (.SD .x21 .x6 (80#12))
  | 42 => .base (.LD .x6 .x8 (152#12))
  | 43 => .base (.SD .x21 .x6 (88#12))
  | 44 => .base (.ADDI .x10 .x21 (0#12))
  | 45 => .base (.ANDI .x7 .x20 (1#12))
  | 46 => .base (.SLLI .x7 .x7 (5#6))
  | 47 => .base (.ADD .x12 .x21 .x7)
  | 48 => .base (.ADDI .x12 .x12 (96#12))
  | 49 => .base .ECALL
  | 50 => .base (.ADDI .x10 .x8 (160#12))
  | 51 => .base (.ADDI .x12 .x12 (32#12))
  | 52 => .base .ECALL
  | 53 => .base (.ANDI .x7 .x20 (1#12))
  | 54 => .base (.BNE .x7 .x0 (24#13))
  | 55 => .base (.SD .x21 .x0 (160#12))
  | 56 => .base (.ADDI .x12 .x21 (168#12))
  | 57 => .base (.ADDI .x10 .x0 (24#12))
  | 58 => .base (.JAL .x1 (704#21))
  | 59 => .base (.JAL .x0 (20#21))
  | 60 => .base (.SD .x21 .x0 (120#12))
  | 61 => .base (.ADDI .x12 .x21 (96#12))
  | 62 => .base (.ADDI .x10 .x0 (24#12))
  | 63 => .base (.JAL .x1 (684#21))
  | 64 => .base (.ADDI .x10 .x21 (96#12))
  | 65 => .base (.ADDI .x12 .x21 (0#12))
  | 66 => .base .ECALL
  | 67 => .base (.SH .x21 .x0 (30#12))
  | 68 => .base (.SD .x21 .x0 (64#12))
  | 69 => .base (.SD .x21 .x0 (72#12))
  | 70 => .base (.SD .x21 .x0 (80#12))
  | 71 => .base (.SD .x21 .x0 (88#12))
  | 72 => .base (.ADDI .x22 .x20 (0#12))
  | 73 => .base (.ADDI .x29 .x2 (0#12))
  | 74 => .base (.ADDI .x30 .x2 (64#12))
  | 75 => .base (.ADDI .x6 .x25 (30#12))
  | 76 => .base (.BLTU .x31 .x6 (620#13))
  | 77 => .base (.ANDI .x7 .x22 (1#12))
  | 78 => .base (.BEQ .x7 .x0 (56#13))
  | 79 => .base (.LD .x6 .x21 (0#12))
  | 80 => .base (.SD .x21 .x6 (32#12))
  | 81 => .base (.LD .x6 .x21 (8#12))
  | 82 => .base (.SD .x21 .x6 (40#12))
  | 83 => .base (.LD .x6 .x21 (16#12))
  | 84 => .base (.SD .x21 .x6 (48#12))
  | 85 => .base (.LD .x6 .x21 (24#12))
  | 86 => .base (.SD .x21 .x6 (56#12))
  | 87 => .base (.ADDI .x12 .x21 (0#12))
  | 88 => .base (.ADDI .x10 .x0 (30#12))
  | 89 => .base (.JAL .x1 (580#21))
  | 90 => .base (.SH .x21 .x0 (30#12))
  | 91 => .base (.JAL .x0 (20#21))
  | 92 => .base (.ADDI .x12 .x21 (32#12))
  | 93 => .base (.ADDI .x10 .x0 (30#12))
  | 94 => .base (.JAL .x1 (560#21))
  | 95 => .base (.SH .x21 .x0 (62#12))
  | 96 => .base (.ADDI .x10 .x21 (0#12))
  | 97 => .base (.ADDI .x12 .x21 (0#12))
  | 98 => .base .ECALL
  | 99 => .base (.ADDI .x6 .x2 (32#12))
  | _ => .base .EBREAK

private def checkInstr1 : Nat → Instruction
  | 0 => .base (.BEQ .x29 .x6 (12#13))
  | 1 => .base (.SH .x21 .x0 (30#12))
  | 2 => .base (.JAL .x0 (16#21))
  | 3 => .base (.LD .x6 .x21 (24#12))
  | 4 => .base (.AND .x6 .x6 .x9)
  | 5 => .base (.SD .x21 .x6 (24#12))
  | 6 => .base (.SRLI .x22 .x22 (1#6))
  | 7 => .base (.ADDI .x29 .x29 (32#12))
  | 8 => .base (.BNE .x29 .x30 (8060#13))
  | 9 => .base (.ADDI .x30 .x2 (512#12))
  | 10 => .base (.ANDI .x7 .x22 (1#12))
  | 11 => .base (.BEQ .x7 .x0 (48#13))
  | 12 => .base (.LD .x6 .x21 (0#12))
  | 13 => .base (.SD .x21 .x6 (32#12))
  | 14 => .base (.LD .x6 .x21 (8#12))
  | 15 => .base (.SD .x21 .x6 (40#12))
  | 16 => .base (.LD .x6 .x21 (16#12))
  | 17 => .base (.SD .x21 .x6 (48#12))
  | 18 => .base (.LD .x6 .x21 (24#12))
  | 19 => .base (.SD .x21 .x6 (56#12))
  | 20 => .base (.ADDI .x12 .x21 (0#12))
  | 21 => .base (.JAL .x1 (480#21))
  | 22 => .base (.JAL .x0 (12#21))
  | 23 => .base (.ADDI .x12 .x21 (32#12))
  | 24 => .base (.JAL .x1 (468#21))
  | 25 => .base (.ADDI .x10 .x21 (0#12))
  | 26 => .base (.ADDI .x12 .x21 (0#12))
  | 27 => .base .ECALL
  | 28 => .base (.LD .x6 .x21 (24#12))
  | 29 => .base (.AND .x6 .x6 .x9)
  | 30 => .base (.SD .x21 .x6 (24#12))
  | 31 => .base (.SRLI .x22 .x22 (1#6))
  | 32 => .base (.ADDI .x29 .x29 (32#12))
  | 33 => .base (.BNE .x29 .x30 (8100#13))
  | 34 => .base (.SRLI .x6 .x22 (1#6))
  | 35 => .base (.ADD .x6 .x22 .x6)
  | 36 => .base (.SLLI .x6 .x6 (5#6))
  | 37 => .base (.ADD .x28 .x19 .x6)
  | 38 => .base (.ADD .x29 .x18 .x22)
  | 39 => .base (.LBU .x7 .x29 (0#12))
  | 40 => .base (.BNE .x7 .x0 (48#13))
  | 41 => .base (.ADDI .x7 .x0 (1#12))
  | 42 => .base (.SB .x29 .x7 (0#12))
  | 43 => .base (.LD .x6 .x21 (0#12))
  | 44 => .base (.SD .x28 .x6 (0#12))
  | 45 => .base (.LD .x6 .x21 (8#12))
  | 46 => .base (.SD .x28 .x6 (8#12))
  | 47 => .base (.LD .x6 .x21 (16#12))
  | 48 => .base (.SD .x28 .x6 (16#12))
  | 49 => .base (.LD .x6 .x21 (24#12))
  | 50 => .base (.SD .x28 .x6 (24#12))
  | 51 => .base (.JAL .x0 (52#21))
  | 52 => .base (.LD .x6 .x21 (0#12))
  | 53 => .base (.LD .x7 .x28 (0#12))
  | 54 => .base (.BNE .x6 .x7 (308#13))
  | 55 => .base (.LD .x6 .x21 (8#12))
  | 56 => .base (.LD .x7 .x28 (8#12))
  | 57 => .base (.BNE .x6 .x7 (296#13))
  | 58 => .base (.LD .x6 .x21 (16#12))
  | 59 => .base (.LD .x7 .x28 (16#12))
  | 60 => .base (.BNE .x6 .x7 (284#13))
  | 61 => .base (.LD .x6 .x21 (24#12))
  | 62 => .base (.LD .x7 .x28 (24#12))
  | 63 => .base (.BNE .x6 .x7 (272#13))
  | 64 => .base (.ADDI .x24 .x24 (8#12))
  | 65 => .base (.ADDI .x8 .x8 (256#12))
  | 66 => .base (.ADDI .x27 .x27 (4095#12))
  | 67 => .base (.BNE .x27 .x0 (7612#13))
  | 68 => .base (.ADDI .x29 .x2 (512#12))
  | 69 => .base (.ADDI .x30 .x2 (768#12))
  | 70 => .base (.LD .x20 .x29 (8#12))
  | 71 => .base (.LD .x14 .x29 (16#12))
  | 72 => .base (.ADD .x14 .x18 .x14)
  | 73 => .base (.LD .x15 .x29 (48#12))
  | 74 => .base (.ADD .x15 .x18 .x15)
  | 75 => .base (.LD .x16 .x29 (24#12))
  | 76 => .base (.ADD .x16 .x19 .x16)
  | 77 => .base (.LD .x17 .x29 (56#12))
  | 78 => .base (.ADD .x17 .x19 .x17)
  | 79 => .base (.SRLI .x22 .x20 (1#6))
  | 80 => .base (.ADDI .x23 .x0 (0#12))
  | 81 => .base (.SLLI .x6 .x23 (1#6))
  | 82 => .base (.ADD .x6 .x14 .x6)
  | 83 => .base (.LBU .x7 .x6 (0#12))
  | 84 => .base (.LBU .x8 .x6 (1#12))
  | 85 => .base (.OR .x28 .x7 .x8)
  | 86 => .base (.BEQ .x28 .x0 (88#13))
  | 87 => .base (.ADD .x6 .x15 .x23)
  | 88 => .base (.SB .x6 .x28 (0#12))
  | 89 => .base (.SLLI .x6 .x23 (6#6))
  | 90 => .base (.SLLI .x28 .x23 (5#6))
  | 91 => .base (.ADD .x10 .x6 .x28)
  | 92 => .base (.ADD .x10 .x16 .x10)
  | 93 => .base (.BEQ .x7 .x8 (20#13))
  | 94 => .base (.ADDI .x12 .x10 (0#12))
  | 95 => .base (.BEQ .x7 .x0 (8#13))
  | 96 => .base (.ADDI .x12 .x10 (32#12))
  | 97 => .base (.JAL .x1 (176#21))
  | 98 => .base (.SRLI .x6 .x23 (1#6))
  | 99 => .base (.ADD .x6 .x23 .x6)
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.SLLI .x6 .x6 (5#6))
  | 1 => .base (.ADD .x12 .x17 .x6)
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x6 .x2 (736#12))
  | 4 => .base (.BEQ .x29 .x6 (16#13))
  | 5 => .base (.LD .x6 .x12 (24#12))
  | 6 => .base (.AND .x6 .x6 .x9)
  | 7 => .base (.SD .x12 .x6 (24#12))
  | 8 => .base (.ADDI .x23 .x23 (1#12))
  | 9 => .base (.BNE .x23 .x22 (8080#13))
  | 10 => .base (.ADDI .x29 .x29 (32#12))
  | 11 => .base (.BNE .x29 .x30 (8028#13))
  | 12 => .base (.BNE .x25 .x31 (76#13))
  | 13 => .base (.BNE .x3 .x0 (72#13))
  | 14 => .base (.LD .x6 .x2 (792#12))
  | 15 => .base (.ADD .x10 .x19 .x6)
  | 16 => .base (.LD .x6 .x10 (0#12))
  | 17 => .base (.LD .x7 .x26 (0#12))
  | 18 => .base (.BNE .x6 .x7 (52#13))
  | 19 => .base (.LD .x6 .x10 (8#12))
  | 20 => .base (.LD .x7 .x26 (8#12))
  | 21 => .base (.BNE .x6 .x7 (40#13))
  | 22 => .base (.LD .x6 .x10 (16#12))
  | 23 => .base (.LD .x7 .x26 (16#12))
  | 24 => .base (.BNE .x6 .x7 (28#13))
  | 25 => .base (.LD .x6 .x10 (24#12))
  | 26 => .base (.LD .x7 .x26 (24#12))
  | 27 => .base (.BNE .x6 .x7 (16#13))
  | 28 => .base (.ADDI .x5 .x0 (1#12))
  | 29 => .base (.ADDI .x10 .x0 (0#12))
  | 30 => .base .ECALL
  | 31 => .base (.ADDI .x5 .x0 (1#12))
  | 32 => .base (.ADDI .x10 .x0 (1#12))
  | 33 => .base .ECALL
  | 34 => .base (.LBU .x6 .x25 (0#12))
  | 35 => .base (.SB .x12 .x6 (0#12))
  | 36 => .base (.ADDI .x25 .x25 (1#12))
  | 37 => .base (.ADDI .x12 .x12 (1#12))
  | 38 => .base (.ADDI .x10 .x10 (4095#12))
  | 39 => .base (.BNE .x10 .x0 (8172#13))
  | 40 => .base (.JALR .x0 .x1 (0#12))
  | 41 => .base (.ADDI .x6 .x25 (29#12))
  | 42 => .base (.BLTU .x31 .x6 (8148#13))
  | 43 => .base (.ADDI .x7 .x0 (29#12))
  | 44 => .base (.LBU .x6 .x25 (0#12))
  | 45 => .base (.SB .x12 .x6 (0#12))
  | 46 => .base (.ADDI .x25 .x25 (1#12))
  | 47 => .base (.ADDI .x12 .x12 (1#12))
  | 48 => .base (.ADDI .x7 .x7 (4095#12))
  | 49 => .base (.BNE .x7 .x0 (8172#13))
  | 50 => .base (.ADDI .x7 .x0 (6#12))
  | 51 => .base (.BGEU .x4 .x7 (28#13))
  | 52 => .base (.BGEU .x25 .x31 (8108#13))
  | 53 => .base (.ADDI .x31 .x31 (4095#12))
  | 54 => .base (.LBU .x6 .x31 (0#12))
  | 55 => .base (.SLL .x6 .x6 .x4)
  | 56 => .base (.OR .x3 .x3 .x6)
  | 57 => .base (.ADDI .x4 .x4 (8#12))
  | 58 => .base (.ANDI .x6 .x3 (63#12))
  | 59 => .base (.SRLI .x3 .x3 (6#6))
  | 60 => .base (.ADDI .x4 .x4 (4090#12))
  | 61 => .base (.SB .x12 .x6 (0#12))
  | 62 => .base (.SB .x12 .x0 (1#12))
  | 63 => .base (.SB .x12 .x0 (2#12))
  | 64 => .base (.JALR .x0 .x1 (0#12))
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

private theorem decode_check_2 (i : Fin 65) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (checkInstr (200 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 265)
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
