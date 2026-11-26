import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨2617246752, 8556390424⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 6912218176, 7046435904, 11341403200⟩ := rfl

theorem commit_dataBase : dataBase (submission.image .commit) = 68719476032 := by
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

theorem commitData_dword_0 (i : Fin 22) :
    packedDword MoonArtifact.commitData (32 * i.val) (by omega) =
      BitVec.ofNat 64 (levelBase (i.val + 1)) := by
  revert i; decide

theorem commitData_dword_1 (i : Fin 22) :
    packedDword MoonArtifact.commitData (32 * i.val + 8) (by omega) =
      BitVec.ofNat 64 (levelBase (i.val + 2)) := by
  revert i; decide

theorem commitData_dword_2 (i : Fin 22) :
    packedDword MoonArtifact.commitData (32 * i.val + 16) (by omega) =
      BitVec.ofNat 64 (levelSize (i.val + 1) / 2) := by
  revert i; decide

theorem commitData_dword_3 (i : Fin 22) :
    packedDword MoonArtifact.commitData (32 * i.val + 24) (by omega) =
      BitVec.ofNat 64 (levelSize (i.val + 1) % 2) := by
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

def l1PairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x06050513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | _ => 0#32

def l1PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (96#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_l1PairWord (j : Fin 6) :
    decodeInstruction (l1PairWord j.val) = some (l1PairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_l1_bulk_words_0 (k : Fin 64) (j : Fin 6) :
    MoonArtifact.commitCode.get 32 ⟨3386 + 6 * (0 + k.val) + j.val, by omega⟩ = l1PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_l1_bulk_words_1 (k : Fin 64) (j : Fin 6) :
    MoonArtifact.commitCode.get 32 ⟨3386 + 6 * (64 + k.val) + j.val, by omega⟩ = l1PairWord j.val := by
  revert k j; decide

theorem commit_fetch_l1_bulk (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (3386 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (l1PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (3386 + 6 * k + j) (by omega)
    (l1PairWord j) hpc _ (l1PairInstr j) (decode_l1PairWord ⟨j, hj⟩)
  by_cases h0 : k < 64
  · simpa using commit_fetch_l1_bulk_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_l1_bulk_words_1 ⟨k - 64, by omega⟩ ⟨j, hj⟩
    simpa [show 64 + (k - 64) = k by omega] using this

def binPairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x00061f23#32
  | 4 => 0x06050513#32
  | 5 => 0x02060613#32
  | 6 => 0x00000073#32
  | 7 => 0x00061f23#32
  | _ => 0#32

def binPairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.SH .x12 .x0 (30#12))
  | 4 => .base (.ADDI .x10 .x10 (96#12))
  | 5 => .base (.ADDI .x12 .x12 (32#12))
  | 6 => .base .ECALL
  | 7 => .base (.SH .x12 .x0 (30#12))
  | _ => .base .EBREAK

theorem decode_binPairWord (j : Fin 8) :
    decodeInstruction (binPairWord j.val) = some (binPairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_bin_bulk_words_0 (k : Fin 32) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨4195 + 8 * (0 + k.val) + j.val, by omega⟩ = binPairWord j.val := by
  revert k j; decide

private theorem commit_fetch_bin_bulk_words_1 (k : Fin 32) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨4195 + 8 * (32 + k.val) + j.val, by omega⟩ = binPairWord j.val := by
  revert k j; decide

theorem commit_fetch_bin_bulk (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4195 + 8 * k + j))) :
    fetch (submission.image .commit) state = some (binPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (4195 + 8 * k + j) (by omega)
    (binPairWord j) hpc _ (binPairInstr j) (decode_binPairWord ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_bin_bulk_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_bin_bulk_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

def bin238PairWord : Nat → BitVec 32
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

def bin238PairInstr : Nat → Instruction
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

theorem decode_bin238PairWord (j : Fin 12) :
    decodeInstruction (bin238PairWord j.val) = some (bin238PairInstr j.val) := by
  revert j; decide

private theorem commit_fetch_bin238_bulk_words_0 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨4766 + 12 * (0 + k.val) + j.val, by omega⟩ = bin238PairWord j.val := by
  revert k j; decide

private theorem commit_fetch_bin238_bulk_words_1 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨4766 + 12 * (32 + k.val) + j.val, by omega⟩ = bin238PairWord j.val := by
  revert k j; decide

theorem commit_fetch_bin238_bulk (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4766 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (bin238PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (4766 + 12 * k + j) (by omega)
    (bin238PairWord j) hpc _ (bin238PairInstr j) (decode_bin238PairWord ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_bin238_bulk_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  ·
    have := commit_fetch_bin238_bulk_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (256#12))
  | 4 => .base (.SLLI .x6 .x6 (11#6))
  | 5 => .base (.SLLI .x6 .x6 (11#6))
  | 6 => .base (.ADDI .x6 .x6 (1056#12))
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
  | 3379 => .base (.ADDI .x12 .x12 (4032#12))
  | 3380 => .base (.ADDI .x6 .x0 (127#12))
  | 3381 => .base (.SLLI .x6 .x6 (11#6))
  | 3382 => .base (.ADDI .x6 .x6 (2043#12))
  | 3383 => .base (.SLLI .x6 .x6 (11#6))
  | 3384 => .base (.ADDI .x6 .x6 (1952#12))
  | 3385 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1CInstr (i : Fin 13) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨3373 + i.val, by omega⟩) =
      some (commitMid1CInstr (3373 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (hlo : 3373 ≤ idx) (hhi : idx < 3386)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  have h := decode_commitMid1CInstr ⟨idx - 3373, by omega⟩
  have heq : 3373 + (idx - 3373) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid2Instr : Nat → Instruction
  | 4154 => .base (.BNE .x10 .x19 (5120#13))
  | 4155 => .base (.ADDI .x6 .x0 (127#12))
  | 4156 => .base (.SLLI .x6 .x6 (11#6))
  | 4157 => .base (.ADDI .x6 .x6 (2047#12))
  | 4158 => .base (.SLLI .x6 .x6 (11#6))
  | 4159 => .base (.ADDI .x6 .x6 (1824#12))
  | 4160 => .base (.ADD .x19 .x9 .x6)
  | 4161 => .base (.ADDI .x10 .x10 (96#12))
  | 4162 => .base (.ADDI .x12 .x12 (64#12))
  | 4163 => .base .ECALL
  | 4164 => .base (.ADDI .x10 .x10 (96#12))
  | 4165 => .base (.ADDI .x12 .x12 (32#12))
  | 4166 => .base .ECALL
  | 4167 => .base (.BNE .x10 .x19 (8168#13))
  | 4168 => .base (.ADDI .x10 .x10 (96#12))
  | 4169 => .base (.ADDI .x12 .x12 (64#12))
  | 4170 => .base .ECALL
  | 4171 => .base (.LD .x6 .x10 (96#12))
  | 4172 => .base (.SD .x12 .x6 (32#12))
  | 4173 => .base (.LD .x6 .x10 (104#12))
  | 4174 => .base (.SD .x12 .x6 (40#12))
  | 4175 => .base (.LD .x6 .x10 (112#12))
  | 4176 => .base (.SD .x12 .x6 (48#12))
  | 4177 => .base (.LD .x6 .x10 (120#12))
  | 4178 => .base (.SD .x12 .x6 (56#12))
  | 4179 => .base (.ADDI .x24 .x2 (0#12))
  | 4180 => .base (.ADDI .x25 .x2 (128#12))
  | 4181 => .base (.LD .x6 .x24 (0#12))
  | 4182 => .base (.ADD .x10 .x9 .x6)
  | 4183 => .base (.ADDI .x10 .x10 (4000#12))
  | 4184 => .base (.LD .x6 .x24 (8#12))
  | 4185 => .base (.ADD .x12 .x9 .x6)
  | 4186 => .base (.ADDI .x12 .x12 (4032#12))
  | 4187 => .base (.LD .x20 .x24 (16#12))
  | 4188 => .base (.LD .x21 .x24 (24#12))
  | 4189 => .base (.SRLI .x22 .x20 (7#6))
  | 4190 => .base (.BEQ .x22 .x0 (2072#13))
  | 4191 => .base (.SLLI .x6 .x22 (12#6))
  | 4192 => .base (.SLLI .x7 .x22 (13#6))
  | 4193 => .base (.ADD .x6 .x6 .x7)
  | 4194 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid2Instr (i : Fin 41) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4154 + i.val, by omega⟩) =
      some (commitMid2Instr (4154 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2Instr (state : MachineState) (idx : Nat) (hlo : 4154 ≤ idx) (hhi : idx < 4195)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2Instr idx) := by
  have h := decode_commitMid2Instr ⟨idx - 4154, by omega⟩
  have heq : 4154 + (idx - 4154) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid3Instr : Nat → Instruction
  | 4707 => .base (.BNE .x10 .x19 (6144#13))
  | 4708 => .base (.ANDI .x22 .x20 (127#12))
  | 4709 => .base (.SRLI .x22 .x22 (1#6))
  | 4710 => .base (.BEQ .x22 .x0 (44#13))
  | 4711 => .base (.ADDI .x10 .x10 (96#12))
  | 4712 => .base (.ADDI .x12 .x12 (64#12))
  | 4713 => .base .ECALL
  | 4714 => .base (.SH .x12 .x0 (30#12))
  | 4715 => .base (.ADDI .x10 .x10 (96#12))
  | 4716 => .base (.ADDI .x12 .x12 (32#12))
  | 4717 => .base .ECALL
  | 4718 => .base (.SH .x12 .x0 (30#12))
  | 4719 => .base (.ADDI .x22 .x22 (4095#12))
  | 4720 => .base (.BNE .x22 .x0 (8156#13))
  | 4721 => .base (.ANDI .x22 .x20 (1#12))
  | 4722 => .base (.BEQ .x22 .x0 (60#13))
  | 4723 => .base (.ADDI .x10 .x10 (96#12))
  | 4724 => .base (.ADDI .x12 .x12 (64#12))
  | 4725 => .base .ECALL
  | 4726 => .base (.SH .x12 .x0 (30#12))
  | 4727 => .base (.BEQ .x21 .x0 (76#13))
  | 4728 => .base (.LD .x6 .x10 (96#12))
  | 4729 => .base (.SD .x12 .x6 (32#12))
  | 4730 => .base (.LD .x6 .x10 (104#12))
  | 4731 => .base (.SD .x12 .x6 (40#12))
  | 4732 => .base (.LD .x6 .x10 (112#12))
  | 4733 => .base (.SD .x12 .x6 (48#12))
  | 4734 => .base (.LD .x6 .x10 (120#12))
  | 4735 => .base (.SD .x12 .x6 (56#12))
  | 4736 => .base (.JAL .x0 (40#21))
  | 4737 => .base (.BEQ .x21 .x0 (36#13))
  | 4738 => .base (.LD .x6 .x10 (96#12))
  | 4739 => .base (.SD .x12 .x6 (64#12))
  | 4740 => .base (.LD .x6 .x10 (104#12))
  | 4741 => .base (.SD .x12 .x6 (72#12))
  | 4742 => .base (.LD .x6 .x10 (112#12))
  | 4743 => .base (.SD .x12 .x6 (80#12))
  | 4744 => .base (.LD .x6 .x10 (120#12))
  | 4745 => .base (.SD .x12 .x6 (88#12))
  | 4746 => .base (.ADDI .x24 .x24 (32#12))
  | 4747 => .base (.BNE .x24 .x25 (5928#13))
  | 4748 => .base (.ADDI .x25 .x2 (704#12))
  | 4749 => .base (.ADDI .x27 .x0 (1#12))
  | 4750 => .base (.SLLI .x27 .x27 (46#6))
  | 4751 => .base (.ADDI .x27 .x27 (4095#12))
  | 4752 => .base (.LD .x6 .x24 (0#12))
  | 4753 => .base (.ADD .x10 .x9 .x6)
  | 4754 => .base (.ADDI .x10 .x10 (4000#12))
  | 4755 => .base (.LD .x6 .x24 (8#12))
  | 4756 => .base (.ADD .x12 .x9 .x6)
  | 4757 => .base (.ADDI .x12 .x12 (4032#12))
  | 4758 => .base (.LD .x20 .x24 (16#12))
  | 4759 => .base (.LD .x21 .x24 (24#12))
  | 4760 => .base (.SRLI .x22 .x20 (7#6))
  | 4761 => .base (.BEQ .x22 .x0 (3096#13))
  | 4762 => .base (.SLLI .x6 .x22 (12#6))
  | 4763 => .base (.SLLI .x7 .x22 (13#6))
  | 4764 => .base (.ADD .x6 .x6 .x7)
  | 4765 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid3Instr (i : Fin 59) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4707 + i.val, by omega⟩) =
      some (commitMid3Instr (4707 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid3Instr (state : MachineState) (idx : Nat) (hlo : 4707 ≤ idx) (hhi : idx < 4766)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid3Instr idx) := by
  have h := decode_commitMid3Instr ⟨idx - 4707, by omega⟩
  have heq : 4707 + (idx - 4707) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitTailInstr : Nat → Instruction
  | 5534 => .base (.BNE .x10 .x19 (5120#13))
  | 5535 => .base (.ANDI .x22 .x20 (127#12))
  | 5536 => .base (.SRLI .x22 .x22 (1#6))
  | 5537 => .base (.BEQ .x22 .x0 (60#13))
  | 5538 => .base (.ADDI .x10 .x10 (96#12))
  | 5539 => .base (.ADDI .x12 .x12 (64#12))
  | 5540 => .base .ECALL
  | 5541 => .base (.LD .x6 .x12 (24#12))
  | 5542 => .base (.AND .x6 .x6 .x27)
  | 5543 => .base (.SD .x12 .x6 (24#12))
  | 5544 => .base (.ADDI .x10 .x10 (96#12))
  | 5545 => .base (.ADDI .x12 .x12 (32#12))
  | 5546 => .base .ECALL
  | 5547 => .base (.LD .x6 .x12 (24#12))
  | 5548 => .base (.AND .x6 .x6 .x27)
  | 5549 => .base (.SD .x12 .x6 (24#12))
  | 5550 => .base (.ADDI .x22 .x22 (4095#12))
  | 5551 => .base (.BNE .x22 .x0 (8140#13))
  | 5552 => .base (.ANDI .x22 .x20 (1#12))
  | 5553 => .base (.BEQ .x22 .x0 (68#13))
  | 5554 => .base (.ADDI .x10 .x10 (96#12))
  | 5555 => .base (.ADDI .x12 .x12 (64#12))
  | 5556 => .base .ECALL
  | 5557 => .base (.LD .x6 .x12 (24#12))
  | 5558 => .base (.AND .x6 .x6 .x27)
  | 5559 => .base (.SD .x12 .x6 (24#12))
  | 5560 => .base (.BEQ .x21 .x0 (76#13))
  | 5561 => .base (.LD .x6 .x10 (96#12))
  | 5562 => .base (.SD .x12 .x6 (32#12))
  | 5563 => .base (.LD .x6 .x10 (104#12))
  | 5564 => .base (.SD .x12 .x6 (40#12))
  | 5565 => .base (.LD .x6 .x10 (112#12))
  | 5566 => .base (.SD .x12 .x6 (48#12))
  | 5567 => .base (.LD .x6 .x10 (120#12))
  | 5568 => .base (.SD .x12 .x6 (56#12))
  | 5569 => .base (.JAL .x0 (40#21))
  | 5570 => .base (.BEQ .x21 .x0 (36#13))
  | 5571 => .base (.LD .x6 .x10 (96#12))
  | 5572 => .base (.SD .x12 .x6 (64#12))
  | 5573 => .base (.LD .x6 .x10 (104#12))
  | 5574 => .base (.SD .x12 .x6 (72#12))
  | 5575 => .base (.LD .x6 .x10 (112#12))
  | 5576 => .base (.SD .x12 .x6 (80#12))
  | 5577 => .base (.LD .x6 .x10 (120#12))
  | 5578 => .base (.SD .x12 .x6 (88#12))
  | 5579 => .base (.ADDI .x24 .x24 (32#12))
  | 5580 => .base (.BNE .x24 .x25 (4880#13))
  | 5581 => .base (.ADDI .x6 .x0 (256#12))
  | 5582 => .base (.SLLI .x6 .x6 (11#6))
  | 5583 => .base (.SLLI .x6 .x6 (11#6))
  | 5584 => .base (.ADDI .x6 .x6 (928#12))
  | 5585 => .base (.ADD .x10 .x9 .x6)
  | 5586 => .base (.ADDI .x6 .x0 (256#12))
  | 5587 => .base (.SLLI .x6 .x6 (11#6))
  | 5588 => .base (.SLLI .x6 .x6 (11#6))
  | 5589 => .base (.ADDI .x6 .x6 (1024#12))
  | 5590 => .base (.ADD .x12 .x9 .x6)
  | 5591 => .base .ECALL
  | 5592 => .base (.LD .x6 .x12 (0#12))
  | 5593 => .base (.SD .x26 .x6 (0#12))
  | 5594 => .base (.LD .x6 .x12 (8#12))
  | 5595 => .base (.SD .x26 .x6 (8#12))
  | 5596 => .base (.LD .x6 .x12 (16#12))
  | 5597 => .base (.SD .x26 .x6 (16#12))
  | 5598 => .base (.LD .x6 .x12 (24#12))
  | 5599 => .base (.SD .x26 .x6 (24#12))
  | 5600 => .base (.ADDI .x5 .x0 (1#12))
  | 5601 => .base (.ADDI .x10 .x0 (0#12))
  | 5602 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 69) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨5534 + i.val, by omega⟩) =
      some (commitTailInstr (5534 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 5534 ≤ idx) (hhi : idx < 5603)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 5534, by omega⟩
  have heq : 5534 + (idx - 5534) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

/-! ### Opening Program (297 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (652#13))
  | 6 => .base (.ADDI .x12 .x0 (0#12))
  | 7 => .base (.ADDI .x13 .x0 (0#12))
  | 8 => .base (.ADDI .x14 .x0 (63#12))
  | 9 => .base (.ADDI .x31 .x0 (2#12))
  | 10 => .base (.SLLI .x31 .x31 (11#6))
  | 11 => .base (.ADDI .x31 .x31 (672#12))
  | 12 => .base (.SLLI .x31 .x31 (11#6))
  | 13 => .base (.ADDI .x31 .x31 (761#12))
  | 14 => .base (.SLLI .x31 .x31 (11#6))
  | 15 => .base (.ADDI .x15 .x31 (0#12))
  | 16 => .base (.ADDI .x16 .x0 (0#12))
  | 17 => .base (.ADDI .x17 .x0 (0#12))
  | 18 => .base (.ADDI .x6 .x0 (256#12))
  | 19 => .base (.SLLI .x6 .x6 (11#6))
  | 20 => .base (.SLLI .x6 .x6 (11#6))
  | 21 => .base (.ADDI .x6 .x6 (1128#12))
  | 22 => .base (.ADD .x18 .x9 .x6)
  | 23 => .base (.ADDI .x19 .x0 (3#12))
  | 24 => .base (.ADDI .x20 .x0 (1#12))
  | 25 => .base (.SLLI .x20 .x20 (11#6))
  | 26 => .base (.ADDI .x20 .x20 (682#12))
  | 27 => .base (.SLLI .x20 .x20 (11#6))
  | 28 => .base (.ADDI .x20 .x20 (1365#12))
  | 29 => .base (.ADDI .x21 .x0 (2#12))
  | 30 => .base (.SLLI .x21 .x21 (11#6))
  | 31 => .base (.LD .x8 .x24 (0#12))
  | 32 => .base (.SRLI .x6 .x8 (1#6))
  | 33 => .base (.SLLI .x7 .x6 (7#6))
  | 34 => .base (.SLLI .x10 .x6 (6#6))
  | 35 => .base (.ADD .x7 .x7 .x10)
  | 36 => .base (.SLLI .x10 .x6 (3#6))
  | 37 => .base (.SUB .x7 .x7 .x10)
  | 38 => .base (.ANDI .x6 .x8 (1#12))
  | 39 => .base (.SLLI .x6 .x6 (4#6))
  | 40 => .base (.ADD .x7 .x7 .x6)
  | 41 => .base (.ADD .x10 .x18 .x7)
  | 42 => .base (.JAL .x1 (520#21))
  | 43 => .base (.DIVU .x22 .x8 .x19)
  | 44 => .base (.REMU .x23 .x8 .x19)
  | 45 => .base (.BEQ .x22 .x20 (88#13))
  | 46 => .base (.SLLI .x6 .x22 (6#6))
  | 47 => .base (.SLLI .x7 .x22 (5#6))
  | 48 => .base (.ADD .x28 .x6 .x7)
  | 49 => .base (.ADD .x28 .x9 .x28)
  | 50 => .base (.BEQ .x23 .x0 (32#13))
  | 51 => .base (.ADDI .x7 .x0 (1#12))
  | 52 => .base (.BEQ .x23 .x7 (44#13))
  | 53 => .base (.ADDI .x10 .x28 (0#12))
  | 54 => .base (.JAL .x1 (552#21))
  | 55 => .base (.ADDI .x10 .x28 (32#12))
  | 56 => .base (.JAL .x1 (544#21))
  | 57 => .base (.JAL .x0 (40#21))
  | 58 => .base (.ADDI .x10 .x28 (32#12))
  | 59 => .base (.JAL .x1 (532#21))
  | 60 => .base (.ADDI .x10 .x28 (64#12))
  | 61 => .base (.JAL .x1 (524#21))
  | 62 => .base (.JAL .x0 (20#21))
  | 63 => .base (.ADDI .x10 .x28 (0#12))
  | 64 => .base (.JAL .x1 (512#21))
  | 65 => .base (.ADDI .x10 .x28 (64#12))
  | 66 => .base (.JAL .x1 (504#21))
  | 67 => .base (.XORI .x28 .x22 (1#12))
  | 68 => .base (.SRLI .x6 .x28 (1#6))
  | 69 => .base (.ADD .x28 .x28 .x6)
  | 70 => .base (.SLLI .x28 .x28 (5#6))
  | 71 => .base (.LD .x6 .x2 (32#12))
  | 72 => .base (.ADD .x10 .x9 .x6)
  | 73 => .base (.ADD .x10 .x10 .x28)
  | 74 => .base (.JAL .x1 (472#21))
  | 75 => .base (.ADDI .x29 .x2 (64#12))
  | 76 => .base (.ADDI .x30 .x2 (192#12))
  | 77 => .base (.SRLI .x22 .x22 (1#6))
  | 78 => .base (.XORI .x28 .x22 (1#12))
  | 79 => .base (.LD .x7 .x29 (8#12))
  | 80 => .base (.BGEU .x28 .x7 (32#13))
  | 81 => .base (.SRLI .x6 .x28 (1#6))
  | 82 => .base (.ADD .x28 .x28 .x6)
  | 83 => .base (.SLLI .x28 .x28 (5#6))
  | 84 => .base (.LD .x6 .x29 (0#12))
  | 85 => .base (.ADD .x10 .x9 .x6)
  | 86 => .base (.ADD .x10 .x10 .x28)
  | 87 => .base (.JAL .x1 (524#21))
  | 88 => .base (.ADDI .x29 .x29 (32#12))
  | 89 => .base (.BNE .x29 .x30 (8144#13))
  | 90 => .base (.ADDI .x30 .x2 (480#12))
  | 91 => .base (.SRLI .x22 .x22 (1#6))
  | 92 => .base (.XORI .x28 .x22 (1#12))
  | 93 => .base (.LD .x7 .x29 (8#12))
  | 94 => .base (.BGEU .x28 .x7 (32#13))
  | 95 => .base (.SRLI .x6 .x28 (1#6))
  | 96 => .base (.ADD .x28 .x28 .x6)
  | 97 => .base (.SLLI .x28 .x28 (5#6))
  | 98 => .base (.LD .x6 .x29 (0#12))
  | 99 => .base (.ADD .x10 .x9 .x6)
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.ADD .x10 .x10 .x28)
  | 1 => .base (.JAL .x1 (604#21))
  | 2 => .base (.ADDI .x29 .x29 (32#12))
  | 3 => .base (.BNE .x29 .x30 (8144#13))
  | 4 => .base (.SRLI .x22 .x22 (1#6))
  | 5 => .base (.ADD .x6 .x21 .x22)
  | 6 => .base (.ADDI .x7 .x0 (1#12))
  | 7 => .base (.SB .x6 .x7 (0#12))
  | 8 => .base (.ADDI .x24 .x24 (8#12))
  | 9 => .base (.ADDI .x27 .x27 (4095#12))
  | 10 => .base (.BNE .x27 .x0 (7876#13))
  | 11 => .base (.ADDI .x29 .x2 (480#12))
  | 12 => .base (.ADDI .x30 .x2 (768#12))
  | 13 => .base (.LD .x18 .x29 (0#12))
  | 14 => .base (.ADD .x18 .x9 .x18)
  | 15 => .base (.LD .x19 .x29 (8#12))
  | 16 => .base (.LD .x20 .x29 (16#12))
  | 17 => .base (.ADD .x20 .x21 .x20)
  | 18 => .base (.LD .x22 .x29 (48#12))
  | 19 => .base (.ADD .x22 .x21 .x22)
  | 20 => .base (.SRLI .x23 .x19 (1#6))
  | 21 => .base (.ADDI .x24 .x0 (0#12))
  | 22 => .base (.SLLI .x6 .x24 (1#6))
  | 23 => .base (.ADD .x6 .x20 .x6)
  | 24 => .base (.LBU .x7 .x6 (0#12))
  | 25 => .base (.LBU .x8 .x6 (1#12))
  | 26 => .base (.OR .x11 .x7 .x8)
  | 27 => .base (.ADD .x6 .x22 .x24)
  | 28 => .base (.SB .x6 .x11 (0#12))
  | 29 => .base (.BEQ .x7 .x8 (32#13))
  | 30 => .base (.SLLI .x6 .x24 (6#6))
  | 31 => .base (.SLLI .x11 .x24 (5#6))
  | 32 => .base (.ADD .x10 .x6 .x11)
  | 33 => .base (.ADD .x10 .x18 .x10)
  | 34 => .base (.BEQ .x7 .x0 (8#13))
  | 35 => .base (.ADDI .x10 .x10 (32#12))
  | 36 => .base (.JAL .x1 (464#21))
  | 37 => .base (.ADDI .x24 .x24 (1#12))
  | 38 => .base (.BNE .x24 .x23 (8128#13))
  | 39 => .base (.ANDI .x6 .x19 (1#12))
  | 40 => .base (.BEQ .x6 .x0 (24#13))
  | 41 => .base (.SLLI .x7 .x23 (1#6))
  | 42 => .base (.ADD .x7 .x20 .x7)
  | 43 => .base (.LBU .x8 .x7 (0#12))
  | 44 => .base (.ADD .x7 .x22 .x23)
  | 45 => .base (.SB .x7 .x8 (0#12))
  | 46 => .base (.ADDI .x29 .x29 (32#12))
  | 47 => .base (.BNE .x29 .x30 (8056#13))
  | 48 => .base (.ADDI .x10 .x25 (0#12))
  | 49 => .base (.BEQ .x13 .x0 (24#13))
  | 50 => .base (.SB .x10 .x12 (0#12))
  | 51 => .base (.ADDI .x10 .x10 (1#12))
  | 52 => .base (.SRLI .x12 .x12 (8#6))
  | 53 => .base (.ADDI .x13 .x13 (4088#12))
  | 54 => .base (.BNE .x13 .x0 (8176#13))
  | 55 => .base (.BEQ .x17 .x0 (12#13))
  | 56 => .base (.SB .x15 .x16 (0#12))
  | 57 => .base (.ADDI .x15 .x15 (1#12))
  | 58 => .base (.BEQ .x15 .x31 (24#13))
  | 59 => .base (.ADDI .x15 .x15 (4095#12))
  | 60 => .base (.LBU .x6 .x15 (0#12))
  | 61 => .base (.SB .x10 .x6 (0#12))
  | 62 => .base (.ADDI .x10 .x10 (1#12))
  | 63 => .base (.BNE .x15 .x31 (8176#13))
  | 64 => .base (.SUB .x11 .x10 .x26)
  | 65 => .base (.ADDI .x5 .x0 (1#12))
  | 66 => .base (.ADDI .x10 .x0 (0#12))
  | 67 => .base .ECALL
  | 68 => .base (.ADDI .x11 .x0 (0#12))
  | 69 => .base (.ADDI .x5 .x0 (1#12))
  | 70 => .base (.ADDI .x10 .x0 (0#12))
  | 71 => .base .ECALL
  | 72 => .base (.LD .x5 .x10 (0#12))
  | 73 => .base (.SLL .x6 .x5 .x13)
  | 74 => .base (.OR .x12 .x12 .x6)
  | 75 => .base (.SD .x25 .x12 (0#12))
  | 76 => .base (.SRLI .x5 .x5 (1#6))
  | 77 => .base (.SRL .x12 .x5 .x14)
  | 78 => .base (.LD .x5 .x10 (8#12))
  | 79 => .base (.SLL .x6 .x5 .x13)
  | 80 => .base (.OR .x12 .x12 .x6)
  | 81 => .base (.SD .x25 .x12 (8#12))
  | 82 => .base (.SRLI .x5 .x5 (1#6))
  | 83 => .base (.SRL .x12 .x5 .x14)
  | 84 => .base (.LD .x5 .x10 (16#12))
  | 85 => .base (.SLL .x6 .x5 .x13)
  | 86 => .base (.OR .x12 .x12 .x6)
  | 87 => .base (.SD .x25 .x12 (16#12))
  | 88 => .base (.SRLI .x5 .x5 (1#6))
  | 89 => .base (.SRL .x12 .x5 .x14)
  | 90 => .base (.ADDI .x25 .x25 (24#12))
  | 91 => .base (.JALR .x0 .x1 (0#12))
  | 92 => .base (.LD .x5 .x10 (0#12))
  | 93 => .base (.SLL .x6 .x5 .x13)
  | 94 => .base (.OR .x12 .x12 .x6)
  | 95 => .base (.SD .x25 .x12 (0#12))
  | 96 => .base (.SRLI .x5 .x5 (1#6))
  | 97 => .base (.SRL .x12 .x5 .x14)
  | 98 => .base (.LD .x5 .x10 (8#12))
  | 99 => .base (.SLL .x6 .x5 .x13)
  | _ => .base .EBREAK

private def openingInstr2 : Nat → Instruction
  | 0 => .base (.OR .x12 .x12 .x6)
  | 1 => .base (.SD .x25 .x12 (8#12))
  | 2 => .base (.SRLI .x5 .x5 (1#6))
  | 3 => .base (.SRL .x12 .x5 .x14)
  | 4 => .base (.LD .x5 .x10 (16#12))
  | 5 => .base (.SLL .x6 .x5 .x13)
  | 6 => .base (.OR .x12 .x12 .x6)
  | 7 => .base (.SD .x25 .x12 (16#12))
  | 8 => .base (.SRLI .x5 .x5 (1#6))
  | 9 => .base (.SRL .x12 .x5 .x14)
  | 10 => .base (.LD .x5 .x10 (24#12))
  | 11 => .base (.SLL .x6 .x5 .x13)
  | 12 => .base (.OR .x12 .x12 .x6)
  | 13 => .base (.SD .x25 .x12 (24#12))
  | 14 => .base (.SRLI .x5 .x5 (1#6))
  | 15 => .base (.SRL .x12 .x5 .x14)
  | 16 => .base (.ADDI .x25 .x25 (32#12))
  | 17 => .base (.JALR .x0 .x1 (0#12))
  | 18 => .base (.LD .x5 .x10 (0#12))
  | 19 => .base (.SLL .x6 .x5 .x13)
  | 20 => .base (.OR .x12 .x12 .x6)
  | 21 => .base (.SD .x25 .x12 (0#12))
  | 22 => .base (.SRLI .x5 .x5 (1#6))
  | 23 => .base (.SRL .x12 .x5 .x14)
  | 24 => .base (.LD .x5 .x10 (8#12))
  | 25 => .base (.SLL .x6 .x5 .x13)
  | 26 => .base (.OR .x12 .x12 .x6)
  | 27 => .base (.SD .x25 .x12 (8#12))
  | 28 => .base (.SRLI .x5 .x5 (1#6))
  | 29 => .base (.SRL .x12 .x5 .x14)
  | 30 => .base (.LD .x5 .x10 (16#12))
  | 31 => .base (.SLL .x6 .x5 .x13)
  | 32 => .base (.OR .x12 .x12 .x6)
  | 33 => .base (.SD .x25 .x12 (16#12))
  | 34 => .base (.SRLI .x5 .x5 (1#6))
  | 35 => .base (.SRL .x12 .x5 .x14)
  | 36 => .base (.ADDI .x25 .x25 (24#12))
  | 37 => .base (.LD .x5 .x10 (24#12))
  | 38 => .base (.SLLI .x5 .x5 (16#6))
  | 39 => .base (.SRLI .x5 .x5 (16#6))
  | 40 => .base (.SLL .x6 .x5 .x13)
  | 41 => .base (.OR .x12 .x12 .x6)
  | 42 => .base (.ADDI .x13 .x13 (48#12))
  | 43 => .base (.ADDI .x7 .x0 (64#12))
  | 44 => .base (.BLTU .x13 .x7 (24#13))
  | 45 => .base (.SD .x25 .x12 (0#12))
  | 46 => .base (.ADDI .x25 .x25 (8#12))
  | 47 => .base (.SRLI .x5 .x5 (1#6))
  | 48 => .base (.SRL .x12 .x5 .x14)
  | 49 => .base (.ADDI .x13 .x13 (4032#12))
  | 50 => .base (.XORI .x14 .x13 (63#12))
  | 51 => .base (.JALR .x0 .x1 (0#12))
  | 52 => .base (.LD .x5 .x10 (0#12))
  | 53 => .base (.SLL .x6 .x5 .x13)
  | 54 => .base (.OR .x12 .x12 .x6)
  | 55 => .base (.SD .x25 .x12 (0#12))
  | 56 => .base (.SRLI .x5 .x5 (1#6))
  | 57 => .base (.SRL .x12 .x5 .x14)
  | 58 => .base (.LD .x5 .x10 (8#12))
  | 59 => .base (.SLL .x6 .x5 .x13)
  | 60 => .base (.OR .x12 .x12 .x6)
  | 61 => .base (.SD .x25 .x12 (8#12))
  | 62 => .base (.SRLI .x5 .x5 (1#6))
  | 63 => .base (.SRL .x12 .x5 .x14)
  | 64 => .base (.LD .x5 .x10 (16#12))
  | 65 => .base (.SLL .x6 .x5 .x13)
  | 66 => .base (.OR .x12 .x12 .x6)
  | 67 => .base (.SD .x25 .x12 (16#12))
  | 68 => .base (.SRLI .x5 .x5 (1#6))
  | 69 => .base (.SRL .x12 .x5 .x14)
  | 70 => .base (.ADDI .x25 .x25 (24#12))
  | 71 => .base (.LD .x11 .x10 (24#12))
  | 72 => .base (.SLLI .x5 .x11 (24#6))
  | 73 => .base (.SRLI .x5 .x5 (24#6))
  | 74 => .base (.SLL .x6 .x5 .x13)
  | 75 => .base (.OR .x12 .x12 .x6)
  | 76 => .base (.ADDI .x13 .x13 (40#12))
  | 77 => .base (.ADDI .x7 .x0 (64#12))
  | 78 => .base (.BLTU .x13 .x7 (24#13))
  | 79 => .base (.SD .x25 .x12 (0#12))
  | 80 => .base (.ADDI .x25 .x25 (8#12))
  | 81 => .base (.SRLI .x5 .x5 (1#6))
  | 82 => .base (.SRL .x12 .x5 .x14)
  | 83 => .base (.ADDI .x13 .x13 (4032#12))
  | 84 => .base (.XORI .x14 .x13 (63#12))
  | 85 => .base (.SRLI .x5 .x11 (40#6))
  | 86 => .base (.ANDI .x5 .x5 (63#12))
  | 87 => .base (.SLL .x6 .x5 .x17)
  | 88 => .base (.OR .x16 .x16 .x6)
  | 89 => .base (.ADDI .x17 .x17 (6#12))
  | 90 => .base (.ADDI .x7 .x0 (8#12))
  | 91 => .base (.BLTU .x17 .x7 (20#13))
  | 92 => .base (.SB .x15 .x16 (0#12))
  | 93 => .base (.ADDI .x15 .x15 (1#12))
  | 94 => .base (.SRLI .x16 .x16 (8#6))
  | 95 => .base (.ADDI .x17 .x17 (4088#12))
  | 96 => .base (.JALR .x0 .x1 (0#12))
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

private theorem decode_opening_2 (i : Fin 97) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (openingInstr (200 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 297)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .opening) state = some (openingInstr idx) := by
  apply fetch_of_packed MoonArtifact.openingCode _ state idx hhi hpc
  by_cases h0 : idx < 100
  · exact decode_opening_0 ⟨idx, h0⟩
  · by_cases h1 : idx < 200
    · have h := decode_opening_1 ⟨idx - 100, by omega⟩
      have heq : 100 + (idx - 100) = idx := by omega
      simpa only [heq] using h
    · have h := decode_opening_2 ⟨idx - 200, by omega⟩
      have heq : 200 + (idx - 200) = idx := by omega
      simpa only [heq] using h

/-! ### Check Program (364 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (1292#13))
  | 8 => .base (.JAL .x0 (1276#21))
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
  | 24 => .base (.BLTU .x31 .x6 (1224#13))
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
  | 58 => .base (.JAL .x1 (1100#21))
  | 59 => .base (.JAL .x0 (20#21))
  | 60 => .base (.SD .x21 .x0 (120#12))
  | 61 => .base (.ADDI .x12 .x21 (96#12))
  | 62 => .base (.ADDI .x10 .x0 (24#12))
  | 63 => .base (.JAL .x1 (1080#21))
  | 64 => .base (.ADDI .x10 .x21 (96#12))
  | 65 => .base (.ADDI .x12 .x21 (0#12))
  | 66 => .base .ECALL
  | 67 => .base (.ADDI .x7 .x0 (3#12))
  | 68 => .base (.DIVU .x22 .x20 .x7)
  | 69 => .base (.REMU .x23 .x20 .x7)
  | 70 => .base (.ADDI .x6 .x0 (1#12))
  | 71 => .base (.SLLI .x6 .x6 (11#6))
  | 72 => .base (.ADDI .x6 .x6 (682#12))
  | 73 => .base (.SLLI .x6 .x6 (11#6))
  | 74 => .base (.ADDI .x6 .x6 (1365#12))
  | 75 => .base (.BEQ .x22 .x6 (156#13))
  | 76 => .base (.ADDI .x6 .x25 (64#12))
  | 77 => .base (.BLTU .x31 .x6 (1012#13))
  | 78 => .base (.BEQ .x23 .x0 (60#13))
  | 79 => .base (.ADDI .x7 .x0 (1#12))
  | 80 => .base (.BEQ .x23 .x7 (68#13))
  | 81 => .base (.LD .x6 .x21 (0#12))
  | 82 => .base (.SD .x21 .x6 (64#12))
  | 83 => .base (.LD .x6 .x21 (8#12))
  | 84 => .base (.SD .x21 .x6 (72#12))
  | 85 => .base (.LD .x6 .x21 (16#12))
  | 86 => .base (.SD .x21 .x6 (80#12))
  | 87 => .base (.LD .x6 .x21 (24#12))
  | 88 => .base (.SD .x21 .x6 (88#12))
  | 89 => .base (.ADDI .x12 .x21 (0#12))
  | 90 => .base (.ADDI .x10 .x0 (64#12))
  | 91 => .base (.JAL .x1 (968#21))
  | 92 => .base (.JAL .x0 (76#21))
  | 93 => .base (.ADDI .x12 .x21 (32#12))
  | 94 => .base (.ADDI .x10 .x0 (64#12))
  | 95 => .base (.JAL .x1 (952#21))
  | 96 => .base (.JAL .x0 (60#21))
  | 97 => .base (.LD .x6 .x21 (0#12))
  | 98 => .base (.SD .x21 .x6 (32#12))
  | 99 => .base (.LD .x6 .x21 (8#12))
  | _ => .base .EBREAK

private def checkInstr1 : Nat → Instruction
  | 0 => .base (.SD .x21 .x6 (40#12))
  | 1 => .base (.LD .x6 .x21 (16#12))
  | 2 => .base (.SD .x21 .x6 (48#12))
  | 3 => .base (.LD .x6 .x21 (24#12))
  | 4 => .base (.SD .x21 .x6 (56#12))
  | 5 => .base (.ADDI .x12 .x21 (0#12))
  | 6 => .base (.ADDI .x10 .x0 (32#12))
  | 7 => .base (.JAL .x1 (904#21))
  | 8 => .base (.ADDI .x12 .x21 (64#12))
  | 9 => .base (.ADDI .x10 .x0 (32#12))
  | 10 => .base (.JAL .x1 (892#21))
  | 11 => .base (.ADDI .x10 .x21 (0#12))
  | 12 => .base (.ADDI .x12 .x21 (0#12))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x6 .x25 (32#12))
  | 15 => .base (.BLTU .x31 .x6 (860#13))
  | 16 => .base (.SD .x21 .x0 (64#12))
  | 17 => .base (.SD .x21 .x0 (72#12))
  | 18 => .base (.SD .x21 .x0 (80#12))
  | 19 => .base (.SD .x21 .x0 (88#12))
  | 20 => .base (.ANDI .x7 .x22 (1#12))
  | 21 => .base (.BEQ .x7 .x0 (52#13))
  | 22 => .base (.LD .x6 .x21 (0#12))
  | 23 => .base (.SD .x21 .x6 (32#12))
  | 24 => .base (.LD .x6 .x21 (8#12))
  | 25 => .base (.SD .x21 .x6 (40#12))
  | 26 => .base (.LD .x6 .x21 (16#12))
  | 27 => .base (.SD .x21 .x6 (48#12))
  | 28 => .base (.LD .x6 .x21 (24#12))
  | 29 => .base (.SD .x21 .x6 (56#12))
  | 30 => .base (.ADDI .x12 .x21 (0#12))
  | 31 => .base (.ADDI .x10 .x0 (32#12))
  | 32 => .base (.JAL .x1 (804#21))
  | 33 => .base (.JAL .x0 (16#21))
  | 34 => .base (.ADDI .x12 .x21 (32#12))
  | 35 => .base (.ADDI .x10 .x0 (32#12))
  | 36 => .base (.JAL .x1 (788#21))
  | 37 => .base (.ADDI .x10 .x21 (0#12))
  | 38 => .base (.ADDI .x12 .x21 (0#12))
  | 39 => .base .ECALL
  | 40 => .base (.SH .x21 .x0 (30#12))
  | 41 => .base (.ADDI .x29 .x2 (64#12))
  | 42 => .base (.ADDI .x30 .x2 (192#12))
  | 43 => .base (.SRLI .x22 .x22 (1#6))
  | 44 => .base (.XORI .x28 .x22 (1#12))
  | 45 => .base (.LD .x7 .x29 (8#12))
  | 46 => .base (.BGEU .x28 .x7 (128#13))
  | 47 => .base (.ADDI .x6 .x25 (30#12))
  | 48 => .base (.BLTU .x31 .x6 (728#13))
  | 49 => .base (.ANDI .x7 .x22 (1#12))
  | 50 => .base (.BEQ .x7 .x0 (56#13))
  | 51 => .base (.LD .x6 .x21 (0#12))
  | 52 => .base (.SD .x21 .x6 (32#12))
  | 53 => .base (.LD .x6 .x21 (8#12))
  | 54 => .base (.SD .x21 .x6 (40#12))
  | 55 => .base (.LD .x6 .x21 (16#12))
  | 56 => .base (.SD .x21 .x6 (48#12))
  | 57 => .base (.LD .x6 .x21 (24#12))
  | 58 => .base (.SD .x21 .x6 (56#12))
  | 59 => .base (.ADDI .x12 .x21 (0#12))
  | 60 => .base (.ADDI .x10 .x0 (30#12))
  | 61 => .base (.JAL .x1 (688#21))
  | 62 => .base (.SH .x21 .x0 (30#12))
  | 63 => .base (.JAL .x0 (20#21))
  | 64 => .base (.ADDI .x12 .x21 (32#12))
  | 65 => .base (.ADDI .x10 .x0 (30#12))
  | 66 => .base (.JAL .x1 (668#21))
  | 67 => .base (.SH .x21 .x0 (62#12))
  | 68 => .base (.ADDI .x10 .x21 (0#12))
  | 69 => .base (.ADDI .x12 .x21 (0#12))
  | 70 => .base .ECALL
  | 71 => .base (.ADDI .x6 .x2 (160#12))
  | 72 => .base (.BEQ .x29 .x6 (12#13))
  | 73 => .base (.SH .x21 .x0 (30#12))
  | 74 => .base (.JAL .x0 (16#21))
  | 75 => .base (.LD .x6 .x21 (24#12))
  | 76 => .base (.AND .x6 .x6 .x9)
  | 77 => .base (.SD .x21 .x6 (24#12))
  | 78 => .base (.ADDI .x29 .x29 (32#12))
  | 79 => .base (.BNE .x29 .x30 (8048#13))
  | 80 => .base (.ADDI .x30 .x2 (480#12))
  | 81 => .base (.SRLI .x22 .x22 (1#6))
  | 82 => .base (.XORI .x28 .x22 (1#12))
  | 83 => .base (.LD .x7 .x29 (8#12))
  | 84 => .base (.BGEU .x28 .x7 (88#13))
  | 85 => .base (.ANDI .x7 .x22 (1#12))
  | 86 => .base (.BEQ .x7 .x0 (48#13))
  | 87 => .base (.LD .x6 .x21 (0#12))
  | 88 => .base (.SD .x21 .x6 (32#12))
  | 89 => .base (.LD .x6 .x21 (8#12))
  | 90 => .base (.SD .x21 .x6 (40#12))
  | 91 => .base (.LD .x6 .x21 (16#12))
  | 92 => .base (.SD .x21 .x6 (48#12))
  | 93 => .base (.LD .x6 .x21 (24#12))
  | 94 => .base (.SD .x21 .x6 (56#12))
  | 95 => .base (.ADDI .x12 .x21 (0#12))
  | 96 => .base (.JAL .x1 (576#21))
  | 97 => .base (.JAL .x0 (12#21))
  | 98 => .base (.ADDI .x12 .x21 (32#12))
  | 99 => .base (.JAL .x1 (564#21))
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x21 (0#12))
  | 1 => .base (.ADDI .x12 .x21 (0#12))
  | 2 => .base .ECALL
  | 3 => .base (.LD .x6 .x21 (24#12))
  | 4 => .base (.AND .x6 .x6 .x9)
  | 5 => .base (.SD .x21 .x6 (24#12))
  | 6 => .base (.ADDI .x29 .x29 (32#12))
  | 7 => .base (.BNE .x29 .x30 (8088#13))
  | 8 => .base (.SRLI .x22 .x22 (1#6))
  | 9 => .base (.SRLI .x6 .x22 (1#6))
  | 10 => .base (.ADD .x6 .x22 .x6)
  | 11 => .base (.SLLI .x6 .x6 (5#6))
  | 12 => .base (.ADD .x28 .x19 .x6)
  | 13 => .base (.ADD .x29 .x18 .x22)
  | 14 => .base (.LBU .x7 .x29 (0#12))
  | 15 => .base (.BNE .x7 .x0 (48#13))
  | 16 => .base (.ADDI .x7 .x0 (1#12))
  | 17 => .base (.SB .x29 .x7 (0#12))
  | 18 => .base (.LD .x6 .x21 (0#12))
  | 19 => .base (.SD .x28 .x6 (0#12))
  | 20 => .base (.LD .x6 .x21 (8#12))
  | 21 => .base (.SD .x28 .x6 (8#12))
  | 22 => .base (.LD .x6 .x21 (16#12))
  | 23 => .base (.SD .x28 .x6 (16#12))
  | 24 => .base (.LD .x6 .x21 (24#12))
  | 25 => .base (.SD .x28 .x6 (24#12))
  | 26 => .base (.JAL .x0 (52#21))
  | 27 => .base (.LD .x6 .x21 (0#12))
  | 28 => .base (.LD .x7 .x28 (0#12))
  | 29 => .base (.BNE .x6 .x7 (404#13))
  | 30 => .base (.LD .x6 .x21 (8#12))
  | 31 => .base (.LD .x7 .x28 (8#12))
  | 32 => .base (.BNE .x6 .x7 (392#13))
  | 33 => .base (.LD .x6 .x21 (16#12))
  | 34 => .base (.LD .x7 .x28 (16#12))
  | 35 => .base (.BNE .x6 .x7 (380#13))
  | 36 => .base (.LD .x6 .x21 (24#12))
  | 37 => .base (.LD .x7 .x28 (24#12))
  | 38 => .base (.BNE .x6 .x7 (368#13))
  | 39 => .base (.ADDI .x24 .x24 (8#12))
  | 40 => .base (.ADDI .x8 .x8 (256#12))
  | 41 => .base (.ADDI .x27 .x27 (4095#12))
  | 42 => .base (.BNE .x27 .x0 (7312#13))
  | 43 => .base (.ADDI .x29 .x2 (480#12))
  | 44 => .base (.ADDI .x30 .x2 (768#12))
  | 45 => .base (.LD .x20 .x29 (8#12))
  | 46 => .base (.LD .x14 .x29 (16#12))
  | 47 => .base (.ADD .x14 .x18 .x14)
  | 48 => .base (.LD .x15 .x29 (48#12))
  | 49 => .base (.ADD .x15 .x18 .x15)
  | 50 => .base (.LD .x16 .x29 (24#12))
  | 51 => .base (.ADD .x16 .x19 .x16)
  | 52 => .base (.LD .x17 .x29 (56#12))
  | 53 => .base (.ADD .x17 .x19 .x17)
  | 54 => .base (.SRLI .x22 .x20 (1#6))
  | 55 => .base (.ADDI .x23 .x0 (0#12))
  | 56 => .base (.SLLI .x6 .x23 (1#6))
  | 57 => .base (.ADD .x6 .x14 .x6)
  | 58 => .base (.LBU .x7 .x6 (0#12))
  | 59 => .base (.LBU .x8 .x6 (1#12))
  | 60 => .base (.OR .x28 .x7 .x8)
  | 61 => .base (.BEQ .x28 .x0 (88#13))
  | 62 => .base (.ADD .x6 .x15 .x23)
  | 63 => .base (.SB .x6 .x28 (0#12))
  | 64 => .base (.SLLI .x6 .x23 (6#6))
  | 65 => .base (.SLLI .x28 .x23 (5#6))
  | 66 => .base (.ADD .x10 .x6 .x28)
  | 67 => .base (.ADD .x10 .x16 .x10)
  | 68 => .base (.BEQ .x7 .x8 (20#13))
  | 69 => .base (.ADDI .x12 .x10 (0#12))
  | 70 => .base (.BEQ .x7 .x0 (8#13))
  | 71 => .base (.ADDI .x12 .x10 (32#12))
  | 72 => .base (.JAL .x1 (272#21))
  | 73 => .base (.SRLI .x6 .x23 (1#6))
  | 74 => .base (.ADD .x6 .x23 .x6)
  | 75 => .base (.SLLI .x6 .x6 (5#6))
  | 76 => .base (.ADD .x12 .x17 .x6)
  | 77 => .base .ECALL
  | 78 => .base (.ADDI .x6 .x2 (736#12))
  | 79 => .base (.BEQ .x29 .x6 (16#13))
  | 80 => .base (.LD .x6 .x12 (24#12))
  | 81 => .base (.AND .x6 .x6 .x9)
  | 82 => .base (.SD .x12 .x6 (24#12))
  | 83 => .base (.ADDI .x23 .x23 (1#12))
  | 84 => .base (.BNE .x23 .x22 (8080#13))
  | 85 => .base (.ANDI .x6 .x20 (1#12))
  | 86 => .base (.BEQ .x6 .x0 (92#13))
  | 87 => .base (.SLLI .x7 .x22 (1#6))
  | 88 => .base (.ADD .x7 .x14 .x7)
  | 89 => .base (.LBU .x8 .x7 (0#12))
  | 90 => .base (.BEQ .x8 .x0 (76#13))
  | 91 => .base (.ADD .x7 .x15 .x22)
  | 92 => .base (.SB .x7 .x8 (0#12))
  | 93 => .base (.SLLI .x6 .x22 (6#6))
  | 94 => .base (.SLLI .x7 .x22 (5#6))
  | 95 => .base (.ADD .x10 .x6 .x7)
  | 96 => .base (.ADD .x10 .x16 .x10)
  | 97 => .base (.SRLI .x6 .x22 (1#6))
  | 98 => .base (.ADD .x6 .x22 .x6)
  | 99 => .base (.SLLI .x6 .x6 (5#6))
  | _ => .base .EBREAK

private def checkInstr3 : Nat → Instruction
  | 0 => .base (.ADD .x12 .x17 .x6)
  | 1 => .base (.LD .x6 .x10 (0#12))
  | 2 => .base (.SD .x12 .x6 (0#12))
  | 3 => .base (.LD .x6 .x10 (8#12))
  | 4 => .base (.SD .x12 .x6 (8#12))
  | 5 => .base (.LD .x6 .x10 (16#12))
  | 6 => .base (.SD .x12 .x6 (16#12))
  | 7 => .base (.LD .x6 .x10 (24#12))
  | 8 => .base (.SD .x12 .x6 (24#12))
  | 9 => .base (.ADDI .x29 .x29 (32#12))
  | 10 => .base (.BNE .x29 .x30 (7932#13))
  | 11 => .base (.BNE .x25 .x31 (76#13))
  | 12 => .base (.BNE .x3 .x0 (72#13))
  | 13 => .base (.LD .x6 .x2 (792#12))
  | 14 => .base (.ADD .x10 .x19 .x6)
  | 15 => .base (.LD .x6 .x10 (0#12))
  | 16 => .base (.LD .x7 .x26 (0#12))
  | 17 => .base (.BNE .x6 .x7 (52#13))
  | 18 => .base (.LD .x6 .x10 (8#12))
  | 19 => .base (.LD .x7 .x26 (8#12))
  | 20 => .base (.BNE .x6 .x7 (40#13))
  | 21 => .base (.LD .x6 .x10 (16#12))
  | 22 => .base (.LD .x7 .x26 (16#12))
  | 23 => .base (.BNE .x6 .x7 (28#13))
  | 24 => .base (.LD .x6 .x10 (24#12))
  | 25 => .base (.LD .x7 .x26 (24#12))
  | 26 => .base (.BNE .x6 .x7 (16#13))
  | 27 => .base (.ADDI .x5 .x0 (1#12))
  | 28 => .base (.ADDI .x10 .x0 (0#12))
  | 29 => .base .ECALL
  | 30 => .base (.ADDI .x5 .x0 (1#12))
  | 31 => .base (.ADDI .x10 .x0 (1#12))
  | 32 => .base .ECALL
  | 33 => .base (.LBU .x6 .x25 (0#12))
  | 34 => .base (.SB .x12 .x6 (0#12))
  | 35 => .base (.ADDI .x25 .x25 (1#12))
  | 36 => .base (.ADDI .x12 .x12 (1#12))
  | 37 => .base (.ADDI .x10 .x10 (4095#12))
  | 38 => .base (.BNE .x10 .x0 (8172#13))
  | 39 => .base (.JALR .x0 .x1 (0#12))
  | 40 => .base (.ADDI .x6 .x25 (29#12))
  | 41 => .base (.BLTU .x31 .x6 (8148#13))
  | 42 => .base (.ADDI .x7 .x0 (29#12))
  | 43 => .base (.LBU .x6 .x25 (0#12))
  | 44 => .base (.SB .x12 .x6 (0#12))
  | 45 => .base (.ADDI .x25 .x25 (1#12))
  | 46 => .base (.ADDI .x12 .x12 (1#12))
  | 47 => .base (.ADDI .x7 .x7 (4095#12))
  | 48 => .base (.BNE .x7 .x0 (8172#13))
  | 49 => .base (.ADDI .x7 .x0 (6#12))
  | 50 => .base (.BGEU .x4 .x7 (28#13))
  | 51 => .base (.BGEU .x25 .x31 (8108#13))
  | 52 => .base (.ADDI .x31 .x31 (4095#12))
  | 53 => .base (.LBU .x6 .x31 (0#12))
  | 54 => .base (.SLL .x6 .x6 .x4)
  | 55 => .base (.OR .x3 .x3 .x6)
  | 56 => .base (.ADDI .x4 .x4 (8#12))
  | 57 => .base (.ANDI .x6 .x3 (63#12))
  | 58 => .base (.SRLI .x3 .x3 (6#6))
  | 59 => .base (.ADDI .x4 .x4 (4090#12))
  | 60 => .base (.SB .x12 .x6 (0#12))
  | 61 => .base (.SB .x12 .x0 (1#12))
  | 62 => .base (.SB .x12 .x0 (2#12))
  | 63 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def checkInstr (idx : Nat) : Instruction :=
  if idx < 100 then checkInstr0 idx
  else if idx < 200 then checkInstr1 (idx - 100)
  else if idx < 300 then checkInstr2 (idx - 200)
  else checkInstr3 (idx - 300)

private theorem decode_check_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨i.val, by omega⟩) =
      some (checkInstr i.val) := by
  revert i; decide

private theorem decode_check_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (checkInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_check_2 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (checkInstr (200 + i.val)) := by
  revert i; decide

private theorem decode_check_3 (i : Fin 64) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨300 + i.val, by omega⟩) =
      some (checkInstr (300 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 364)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .check) state = some (checkInstr idx) := by
  apply fetch_of_packed MoonArtifact.checkCode _ state idx hhi hpc
  by_cases h0 : idx < 100
  · exact decode_check_0 ⟨idx, h0⟩
  · by_cases h1 : idx < 200
    · have h := decode_check_1 ⟨idx - 100, by omega⟩
      have heq : 100 + (idx - 100) = idx := by omega
      simpa only [heq] using h
    · by_cases h2 : idx < 300
      · have h := decode_check_2 ⟨idx - 200, by omega⟩
        have heq : 200 + (idx - 200) = idx := by omega
        simpa only [heq] using h
      · have h := decode_check_3 ⟨idx - 300, by omega⟩
        have heq : 300 + (idx - 300) = idx := by omega
        simpa only [heq] using h

end CommitGolfCandidate
