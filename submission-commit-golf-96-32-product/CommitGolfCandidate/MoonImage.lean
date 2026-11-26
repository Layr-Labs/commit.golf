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
  | 4180 => .base (.ADDI .x25 .x2 (704#12))
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

def commitTailInstr : Nat → Instruction
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
  | 4748 => .base (.ADDI .x6 .x0 (256#12))
  | 4749 => .base (.SLLI .x6 .x6 (11#6))
  | 4750 => .base (.SLLI .x6 .x6 (11#6))
  | 4751 => .base (.ADDI .x6 .x6 (928#12))
  | 4752 => .base (.ADD .x10 .x9 .x6)
  | 4753 => .base (.ADDI .x6 .x0 (256#12))
  | 4754 => .base (.SLLI .x6 .x6 (11#6))
  | 4755 => .base (.SLLI .x6 .x6 (11#6))
  | 4756 => .base (.ADDI .x6 .x6 (1024#12))
  | 4757 => .base (.ADD .x12 .x9 .x6)
  | 4758 => .base .ECALL
  | 4759 => .base (.LD .x6 .x12 (0#12))
  | 4760 => .base (.SD .x26 .x6 (0#12))
  | 4761 => .base (.LD .x6 .x12 (8#12))
  | 4762 => .base (.SD .x26 .x6 (8#12))
  | 4763 => .base (.LD .x6 .x12 (16#12))
  | 4764 => .base (.SD .x26 .x6 (16#12))
  | 4765 => .base (.LD .x6 .x12 (24#12))
  | 4766 => .base (.SD .x26 .x6 (24#12))
  | 4767 => .base (.ADDI .x5 .x0 (1#12))
  | 4768 => .base (.ADDI .x10 .x0 (0#12))
  | 4769 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 63) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨4707 + i.val, by omega⟩) =
      some (commitTailInstr (4707 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 4707 ≤ idx) (hhi : idx < 4770)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 4707, by omega⟩
  have heq : 4707 + (idx - 4707) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

/-! ### Opening Program (225 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (508#13))
  | 6 => .base (.ADDI .x6 .x0 (256#12))
  | 7 => .base (.SLLI .x6 .x6 (11#6))
  | 8 => .base (.SLLI .x6 .x6 (11#6))
  | 9 => .base (.ADDI .x6 .x6 (1128#12))
  | 10 => .base (.ADD .x18 .x9 .x6)
  | 11 => .base (.ADDI .x19 .x0 (3#12))
  | 12 => .base (.ADDI .x20 .x0 (1#12))
  | 13 => .base (.SLLI .x20 .x20 (11#6))
  | 14 => .base (.ADDI .x20 .x20 (682#12))
  | 15 => .base (.SLLI .x20 .x20 (11#6))
  | 16 => .base (.ADDI .x20 .x20 (1365#12))
  | 17 => .base (.ADDI .x21 .x0 (2#12))
  | 18 => .base (.SLLI .x21 .x21 (11#6))
  | 19 => .base (.LD .x8 .x24 (0#12))
  | 20 => .base (.SRLI .x6 .x8 (1#6))
  | 21 => .base (.SLLI .x7 .x6 (7#6))
  | 22 => .base (.SLLI .x10 .x6 (6#6))
  | 23 => .base (.ADD .x7 .x7 .x10)
  | 24 => .base (.SLLI .x10 .x6 (3#6))
  | 25 => .base (.SUB .x7 .x7 .x10)
  | 26 => .base (.ANDI .x6 .x8 (1#12))
  | 27 => .base (.SLLI .x6 .x6 (4#6))
  | 28 => .base (.ADD .x7 .x7 .x6)
  | 29 => .base (.ADD .x10 .x18 .x7)
  | 30 => .base (.JAL .x1 (424#21))
  | 31 => .base (.ADDI .x25 .x25 (24#12))
  | 32 => .base (.DIVU .x22 .x8 .x19)
  | 33 => .base (.REMU .x23 .x8 .x19)
  | 34 => .base (.BEQ .x22 .x20 (112#13))
  | 35 => .base (.SLLI .x6 .x22 (6#6))
  | 36 => .base (.SLLI .x7 .x22 (5#6))
  | 37 => .base (.ADD .x28 .x6 .x7)
  | 38 => .base (.ADD .x28 .x9 .x28)
  | 39 => .base (.BEQ .x23 .x0 (40#13))
  | 40 => .base (.ADDI .x7 .x0 (1#12))
  | 41 => .base (.BEQ .x23 .x7 (60#13))
  | 42 => .base (.ADDI .x10 .x28 (0#12))
  | 43 => .base (.JAL .x1 (596#21))
  | 44 => .base (.ADDI .x25 .x25 (32#12))
  | 45 => .base (.ADDI .x10 .x28 (32#12))
  | 46 => .base (.JAL .x1 (584#21))
  | 47 => .base (.ADDI .x25 .x25 (32#12))
  | 48 => .base (.JAL .x0 (56#21))
  | 49 => .base (.ADDI .x10 .x28 (32#12))
  | 50 => .base (.JAL .x1 (568#21))
  | 51 => .base (.ADDI .x25 .x25 (32#12))
  | 52 => .base (.ADDI .x10 .x28 (64#12))
  | 53 => .base (.JAL .x1 (556#21))
  | 54 => .base (.ADDI .x25 .x25 (32#12))
  | 55 => .base (.JAL .x0 (28#21))
  | 56 => .base (.ADDI .x10 .x28 (0#12))
  | 57 => .base (.JAL .x1 (540#21))
  | 58 => .base (.ADDI .x25 .x25 (32#12))
  | 59 => .base (.ADDI .x10 .x28 (64#12))
  | 60 => .base (.JAL .x1 (528#21))
  | 61 => .base (.ADDI .x25 .x25 (32#12))
  | 62 => .base (.XORI .x28 .x22 (1#12))
  | 63 => .base (.SRLI .x6 .x28 (1#6))
  | 64 => .base (.ADD .x28 .x28 .x6)
  | 65 => .base (.SLLI .x28 .x28 (5#6))
  | 66 => .base (.LD .x6 .x2 (32#12))
  | 67 => .base (.ADD .x10 .x9 .x6)
  | 68 => .base (.ADD .x10 .x10 .x28)
  | 69 => .base (.JAL .x1 (492#21))
  | 70 => .base (.ADDI .x25 .x25 (32#12))
  | 71 => .base (.ADDI .x29 .x2 (64#12))
  | 72 => .base (.ADDI .x30 .x2 (480#12))
  | 73 => .base (.SRLI .x22 .x22 (1#6))
  | 74 => .base (.XORI .x28 .x22 (1#12))
  | 75 => .base (.LD .x7 .x29 (8#12))
  | 76 => .base (.BGEU .x28 .x7 (36#13))
  | 77 => .base (.SRLI .x6 .x28 (1#6))
  | 78 => .base (.ADD .x28 .x28 .x6)
  | 79 => .base (.SLLI .x28 .x28 (5#6))
  | 80 => .base (.LD .x6 .x29 (0#12))
  | 81 => .base (.ADD .x10 .x9 .x6)
  | 82 => .base (.ADD .x10 .x10 .x28)
  | 83 => .base (.JAL .x1 (312#21))
  | 84 => .base (.ADDI .x25 .x25 (30#12))
  | 85 => .base (.ADDI .x29 .x29 (32#12))
  | 86 => .base (.BNE .x29 .x30 (8140#13))
  | 87 => .base (.SRLI .x22 .x22 (1#6))
  | 88 => .base (.ADD .x6 .x21 .x22)
  | 89 => .base (.ADDI .x7 .x0 (1#12))
  | 90 => .base (.SB .x6 .x7 (0#12))
  | 91 => .base (.ADDI .x24 .x24 (8#12))
  | 92 => .base (.ADDI .x27 .x27 (4095#12))
  | 93 => .base (.BNE .x27 .x0 (7896#13))
  | 94 => .base (.ADDI .x29 .x2 (480#12))
  | 95 => .base (.ADDI .x30 .x2 (768#12))
  | 96 => .base (.LD .x18 .x29 (0#12))
  | 97 => .base (.ADD .x18 .x9 .x18)
  | 98 => .base (.LD .x19 .x29 (8#12))
  | 99 => .base (.LD .x20 .x29 (16#12))
  | 100 => .base (.ADD .x20 .x21 .x20)
  | 101 => .base (.LD .x22 .x29 (48#12))
  | 102 => .base (.ADD .x22 .x21 .x22)
  | 103 => .base (.SRLI .x23 .x19 (1#6))
  | 104 => .base (.ADDI .x24 .x0 (0#12))
  | 105 => .base (.SLLI .x6 .x24 (1#6))
  | 106 => .base (.ADD .x6 .x20 .x6)
  | 107 => .base (.LBU .x7 .x6 (0#12))
  | 108 => .base (.LBU .x8 .x6 (1#12))
  | 109 => .base (.OR .x11 .x7 .x8)
  | 110 => .base (.ADD .x6 .x22 .x24)
  | 111 => .base (.SB .x6 .x11 (0#12))
  | 112 => .base (.BEQ .x7 .x8 (36#13))
  | 113 => .base (.SLLI .x6 .x24 (6#6))
  | 114 => .base (.SLLI .x11 .x24 (5#6))
  | 115 => .base (.ADD .x10 .x6 .x11)
  | 116 => .base (.ADD .x10 .x18 .x10)
  | 117 => .base (.BEQ .x7 .x0 (8#13))
  | 118 => .base (.ADDI .x10 .x10 (32#12))
  | 119 => .base (.JAL .x1 (168#21))
  | 120 => .base (.ADDI .x25 .x25 (30#12))
  | 121 => .base (.ADDI .x24 .x24 (1#12))
  | 122 => .base (.BNE .x24 .x23 (8124#13))
  | 123 => .base (.ANDI .x6 .x19 (1#12))
  | 124 => .base (.BEQ .x6 .x0 (24#13))
  | 125 => .base (.SLLI .x7 .x23 (1#6))
  | 126 => .base (.ADD .x7 .x20 .x7)
  | 127 => .base (.LBU .x8 .x7 (0#12))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.ADD .x7 .x22 .x23)
  | 1 => .base (.SB .x7 .x8 (0#12))
  | 2 => .base (.ADDI .x29 .x29 (32#12))
  | 3 => .base (.BNE .x29 .x30 (8052#13))
  | 4 => .base (.SUB .x11 .x25 .x26)
  | 5 => .base (.ADDI .x5 .x0 (1#12))
  | 6 => .base (.ADDI .x10 .x0 (0#12))
  | 7 => .base .ECALL
  | 8 => .base (.LHU .x6 .x10 (0#12))
  | 9 => .base (.SH .x25 .x6 (0#12))
  | 10 => .base (.LHU .x6 .x10 (2#12))
  | 11 => .base (.SH .x25 .x6 (2#12))
  | 12 => .base (.LHU .x6 .x10 (4#12))
  | 13 => .base (.SH .x25 .x6 (4#12))
  | 14 => .base (.LHU .x6 .x10 (6#12))
  | 15 => .base (.SH .x25 .x6 (6#12))
  | 16 => .base (.LHU .x6 .x10 (8#12))
  | 17 => .base (.SH .x25 .x6 (8#12))
  | 18 => .base (.LHU .x6 .x10 (10#12))
  | 19 => .base (.SH .x25 .x6 (10#12))
  | 20 => .base (.LHU .x6 .x10 (12#12))
  | 21 => .base (.SH .x25 .x6 (12#12))
  | 22 => .base (.LHU .x6 .x10 (14#12))
  | 23 => .base (.SH .x25 .x6 (14#12))
  | 24 => .base (.LHU .x6 .x10 (16#12))
  | 25 => .base (.SH .x25 .x6 (16#12))
  | 26 => .base (.LHU .x6 .x10 (18#12))
  | 27 => .base (.SH .x25 .x6 (18#12))
  | 28 => .base (.LHU .x6 .x10 (20#12))
  | 29 => .base (.SH .x25 .x6 (20#12))
  | 30 => .base (.LHU .x6 .x10 (22#12))
  | 31 => .base (.SH .x25 .x6 (22#12))
  | 32 => .base (.JALR .x0 .x1 (0#12))
  | 33 => .base (.LHU .x6 .x10 (0#12))
  | 34 => .base (.SH .x25 .x6 (0#12))
  | 35 => .base (.LHU .x6 .x10 (2#12))
  | 36 => .base (.SH .x25 .x6 (2#12))
  | 37 => .base (.LHU .x6 .x10 (4#12))
  | 38 => .base (.SH .x25 .x6 (4#12))
  | 39 => .base (.LHU .x6 .x10 (6#12))
  | 40 => .base (.SH .x25 .x6 (6#12))
  | 41 => .base (.LHU .x6 .x10 (8#12))
  | 42 => .base (.SH .x25 .x6 (8#12))
  | 43 => .base (.LHU .x6 .x10 (10#12))
  | 44 => .base (.SH .x25 .x6 (10#12))
  | 45 => .base (.LHU .x6 .x10 (12#12))
  | 46 => .base (.SH .x25 .x6 (12#12))
  | 47 => .base (.LHU .x6 .x10 (14#12))
  | 48 => .base (.SH .x25 .x6 (14#12))
  | 49 => .base (.LHU .x6 .x10 (16#12))
  | 50 => .base (.SH .x25 .x6 (16#12))
  | 51 => .base (.LHU .x6 .x10 (18#12))
  | 52 => .base (.SH .x25 .x6 (18#12))
  | 53 => .base (.LHU .x6 .x10 (20#12))
  | 54 => .base (.SH .x25 .x6 (20#12))
  | 55 => .base (.LHU .x6 .x10 (22#12))
  | 56 => .base (.SH .x25 .x6 (22#12))
  | 57 => .base (.LHU .x6 .x10 (24#12))
  | 58 => .base (.SH .x25 .x6 (24#12))
  | 59 => .base (.LHU .x6 .x10 (26#12))
  | 60 => .base (.SH .x25 .x6 (26#12))
  | 61 => .base (.LHU .x6 .x10 (28#12))
  | 62 => .base (.SH .x25 .x6 (28#12))
  | 63 => .base (.JALR .x0 .x1 (0#12))
  | 64 => .base (.LHU .x6 .x10 (0#12))
  | 65 => .base (.SH .x25 .x6 (0#12))
  | 66 => .base (.LHU .x6 .x10 (2#12))
  | 67 => .base (.SH .x25 .x6 (2#12))
  | 68 => .base (.LHU .x6 .x10 (4#12))
  | 69 => .base (.SH .x25 .x6 (4#12))
  | 70 => .base (.LHU .x6 .x10 (6#12))
  | 71 => .base (.SH .x25 .x6 (6#12))
  | 72 => .base (.LHU .x6 .x10 (8#12))
  | 73 => .base (.SH .x25 .x6 (8#12))
  | 74 => .base (.LHU .x6 .x10 (10#12))
  | 75 => .base (.SH .x25 .x6 (10#12))
  | 76 => .base (.LHU .x6 .x10 (12#12))
  | 77 => .base (.SH .x25 .x6 (12#12))
  | 78 => .base (.LHU .x6 .x10 (14#12))
  | 79 => .base (.SH .x25 .x6 (14#12))
  | 80 => .base (.LHU .x6 .x10 (16#12))
  | 81 => .base (.SH .x25 .x6 (16#12))
  | 82 => .base (.LHU .x6 .x10 (18#12))
  | 83 => .base (.SH .x25 .x6 (18#12))
  | 84 => .base (.LHU .x6 .x10 (20#12))
  | 85 => .base (.SH .x25 .x6 (20#12))
  | 86 => .base (.LHU .x6 .x10 (22#12))
  | 87 => .base (.SH .x25 .x6 (22#12))
  | 88 => .base (.LHU .x6 .x10 (24#12))
  | 89 => .base (.SH .x25 .x6 (24#12))
  | 90 => .base (.LHU .x6 .x10 (26#12))
  | 91 => .base (.SH .x25 .x6 (26#12))
  | 92 => .base (.LHU .x6 .x10 (28#12))
  | 93 => .base (.SH .x25 .x6 (28#12))
  | 94 => .base (.LHU .x6 .x10 (30#12))
  | 95 => .base (.SH .x25 .x6 (30#12))
  | 96 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def openingInstr (idx : Nat) : Instruction :=
  if idx < 128 then openingInstr0 idx else openingInstr1 (idx - 128)

private theorem decode_opening_0 (i : Fin 128) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr i.val) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 97) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨128 + i.val, by omega⟩) =
      some (openingInstr (128 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 225)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .opening) state = some (openingInstr idx) := by
  apply fetch_of_packed MoonArtifact.openingCode _ state idx hhi hpc
  by_cases h0 : idx < 128
  · exact decode_opening_0 ⟨idx, h0⟩
  · have h := decode_opening_1 ⟨idx - 128, by omega⟩
    have heq : 128 + (idx - 128) = idx := by omega
    simpa only [heq] using h

/-! ### Check Program (388 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (1156#13))
  | 8 => .base (.JAL .x0 (1140#21))
  | 9 => .base (.ADDI .x21 .x0 (256#12))
  | 10 => .base (.ADDI .x18 .x0 (2#12))
  | 11 => .base (.SLLI .x18 .x18 (11#6))
  | 12 => .base (.ADDI .x19 .x0 (4#12))
  | 13 => .base (.SLLI .x19 .x19 (11#6))
  | 14 => .base (.ADDI .x5 .x0 (0#12))
  | 15 => .base (.ADDI .x11 .x0 (96#12))
  | 16 => .base (.ADDI .x13 .x0 (0#12))
  | 17 => .base (.LD .x20 .x24 (0#12))
  | 18 => .base (.ADDI .x6 .x25 (24#12))
  | 19 => .base (.BLTU .x31 .x6 (1108#13))
  | 20 => .base (.ADDI .x10 .x8 (0#12))
  | 21 => .base (.ADDI .x12 .x21 (0#12))
  | 22 => .base .ECALL
  | 23 => .base (.LD .x6 .x8 (96#12))
  | 24 => .base (.SD .x21 .x6 (32#12))
  | 25 => .base (.LD .x6 .x8 (104#12))
  | 26 => .base (.SD .x21 .x6 (40#12))
  | 27 => .base (.LD .x6 .x8 (112#12))
  | 28 => .base (.SD .x21 .x6 (48#12))
  | 29 => .base (.LD .x6 .x8 (120#12))
  | 30 => .base (.SD .x21 .x6 (56#12))
  | 31 => .base (.LD .x6 .x8 (128#12))
  | 32 => .base (.SD .x21 .x6 (64#12))
  | 33 => .base (.LD .x6 .x8 (136#12))
  | 34 => .base (.SD .x21 .x6 (72#12))
  | 35 => .base (.LD .x6 .x8 (144#12))
  | 36 => .base (.SD .x21 .x6 (80#12))
  | 37 => .base (.LD .x6 .x8 (152#12))
  | 38 => .base (.SD .x21 .x6 (88#12))
  | 39 => .base (.ADDI .x10 .x21 (0#12))
  | 40 => .base (.ANDI .x7 .x20 (1#12))
  | 41 => .base (.SLLI .x7 .x7 (5#6))
  | 42 => .base (.ADD .x12 .x21 .x7)
  | 43 => .base (.ADDI .x12 .x12 (96#12))
  | 44 => .base .ECALL
  | 45 => .base (.ADDI .x10 .x8 (160#12))
  | 46 => .base (.ADDI .x12 .x12 (32#12))
  | 47 => .base .ECALL
  | 48 => .base (.ANDI .x7 .x20 (1#12))
  | 49 => .base (.BNE .x7 .x0 (20#13))
  | 50 => .base (.SD .x21 .x0 (160#12))
  | 51 => .base (.ADDI .x12 .x21 (168#12))
  | 52 => .base (.JAL .x1 (988#21))
  | 53 => .base (.JAL .x0 (16#21))
  | 54 => .base (.SD .x21 .x0 (120#12))
  | 55 => .base (.ADDI .x12 .x21 (96#12))
  | 56 => .base (.JAL .x1 (972#21))
  | 57 => .base (.ADDI .x25 .x25 (24#12))
  | 58 => .base (.ADDI .x10 .x21 (96#12))
  | 59 => .base (.ADDI .x12 .x21 (0#12))
  | 60 => .base .ECALL
  | 61 => .base (.ADDI .x7 .x0 (3#12))
  | 62 => .base (.DIVU .x22 .x20 .x7)
  | 63 => .base (.REMU .x23 .x20 .x7)
  | 64 => .base (.ADDI .x6 .x0 (1#12))
  | 65 => .base (.SLLI .x6 .x6 (11#6))
  | 66 => .base (.ADDI .x6 .x6 (682#12))
  | 67 => .base (.SLLI .x6 .x6 (11#6))
  | 68 => .base (.ADDI .x6 .x6 (1365#12))
  | 69 => .base (.BEQ .x22 .x6 (180#13))
  | 70 => .base (.ADDI .x6 .x25 (64#12))
  | 71 => .base (.BLTU .x31 .x6 (900#13))
  | 72 => .base (.BEQ .x23 .x0 (72#13))
  | 73 => .base (.ADDI .x7 .x0 (1#12))
  | 74 => .base (.BEQ .x23 .x7 (92#13))
  | 75 => .base (.LD .x6 .x21 (0#12))
  | 76 => .base (.SD .x21 .x6 (64#12))
  | 77 => .base (.LD .x6 .x21 (8#12))
  | 78 => .base (.SD .x21 .x6 (72#12))
  | 79 => .base (.LD .x6 .x21 (16#12))
  | 80 => .base (.SD .x21 .x6 (80#12))
  | 81 => .base (.LD .x6 .x21 (24#12))
  | 82 => .base (.SD .x21 .x6 (88#12))
  | 83 => .base (.ADDI .x12 .x21 (0#12))
  | 84 => .base (.JAL .x1 (1084#21))
  | 85 => .base (.ADDI .x25 .x25 (32#12))
  | 86 => .base (.ADDI .x12 .x21 (32#12))
  | 87 => .base (.JAL .x1 (1072#21))
  | 88 => .base (.ADDI .x25 .x25 (32#12))
  | 89 => .base (.JAL .x0 (88#21))
  | 90 => .base (.ADDI .x12 .x21 (32#12))
  | 91 => .base (.JAL .x1 (1056#21))
  | 92 => .base (.ADDI .x25 .x25 (32#12))
  | 93 => .base (.ADDI .x12 .x21 (64#12))
  | 94 => .base (.JAL .x1 (1044#21))
  | 95 => .base (.ADDI .x25 .x25 (32#12))
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
  | 6 => .base (.JAL .x1 (996#21))
  | 7 => .base (.ADDI .x25 .x25 (32#12))
  | 8 => .base (.ADDI .x12 .x21 (64#12))
  | 9 => .base (.JAL .x1 (984#21))
  | 10 => .base (.ADDI .x25 .x25 (32#12))
  | 11 => .base (.ADDI .x10 .x21 (0#12))
  | 12 => .base (.ADDI .x12 .x21 (0#12))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x6 .x25 (32#12))
  | 15 => .base (.BLTU .x31 .x6 (724#13))
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
  | 31 => .base (.JAL .x1 (896#21))
  | 32 => .base (.ADDI .x25 .x25 (32#12))
  | 33 => .base (.JAL .x0 (16#21))
  | 34 => .base (.ADDI .x12 .x21 (32#12))
  | 35 => .base (.JAL .x1 (880#21))
  | 36 => .base (.ADDI .x25 .x25 (32#12))
  | 37 => .base (.ADDI .x10 .x21 (0#12))
  | 38 => .base (.ADDI .x12 .x21 (0#12))
  | 39 => .base .ECALL
  | 40 => .base (.SH .x21 .x0 (30#12))
  | 41 => .base (.ADDI .x29 .x2 (64#12))
  | 42 => .base (.ADDI .x30 .x2 (480#12))
  | 43 => .base (.SRLI .x22 .x22 (1#6))
  | 44 => .base (.XORI .x28 .x22 (1#12))
  | 45 => .base (.LD .x7 .x29 (8#12))
  | 46 => .base (.BGEU .x28 .x7 (104#13))
  | 47 => .base (.ADDI .x6 .x25 (30#12))
  | 48 => .base (.BLTU .x31 .x6 (592#13))
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
  | 60 => .base (.JAL .x1 (656#21))
  | 61 => .base (.SH .x21 .x0 (30#12))
  | 62 => .base (.ADDI .x25 .x25 (30#12))
  | 63 => .base (.JAL .x0 (20#21))
  | 64 => .base (.ADDI .x12 .x21 (32#12))
  | 65 => .base (.JAL .x1 (636#21))
  | 66 => .base (.SH .x21 .x0 (62#12))
  | 67 => .base (.ADDI .x25 .x25 (30#12))
  | 68 => .base (.ADDI .x10 .x21 (0#12))
  | 69 => .base (.ADDI .x12 .x21 (0#12))
  | 70 => .base .ECALL
  | 71 => .base (.SH .x21 .x0 (30#12))
  | 72 => .base (.ADDI .x29 .x29 (32#12))
  | 73 => .base (.BNE .x29 .x30 (8072#13))
  | 74 => .base (.SRLI .x22 .x22 (1#6))
  | 75 => .base (.SRLI .x6 .x22 (1#6))
  | 76 => .base (.ADD .x6 .x22 .x6)
  | 77 => .base (.SLLI .x6 .x6 (5#6))
  | 78 => .base (.ADD .x28 .x19 .x6)
  | 79 => .base (.ADD .x29 .x18 .x22)
  | 80 => .base (.LBU .x7 .x29 (0#12))
  | 81 => .base (.BNE .x7 .x0 (48#13))
  | 82 => .base (.ADDI .x7 .x0 (1#12))
  | 83 => .base (.SB .x29 .x7 (0#12))
  | 84 => .base (.LD .x6 .x21 (0#12))
  | 85 => .base (.SD .x28 .x6 (0#12))
  | 86 => .base (.LD .x6 .x21 (8#12))
  | 87 => .base (.SD .x28 .x6 (8#12))
  | 88 => .base (.LD .x6 .x21 (16#12))
  | 89 => .base (.SD .x28 .x6 (16#12))
  | 90 => .base (.LD .x6 .x21 (24#12))
  | 91 => .base (.SD .x28 .x6 (24#12))
  | 92 => .base (.JAL .x0 (52#21))
  | 93 => .base (.LD .x6 .x21 (0#12))
  | 94 => .base (.LD .x7 .x28 (0#12))
  | 95 => .base (.BNE .x6 .x7 (404#13))
  | 96 => .base (.LD .x6 .x21 (8#12))
  | 97 => .base (.LD .x7 .x28 (8#12))
  | 98 => .base (.BNE .x6 .x7 (392#13))
  | 99 => .base (.LD .x6 .x21 (16#12))
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.LD .x7 .x28 (16#12))
  | 1 => .base (.BNE .x6 .x7 (380#13))
  | 2 => .base (.LD .x6 .x21 (24#12))
  | 3 => .base (.LD .x7 .x28 (24#12))
  | 4 => .base (.BNE .x6 .x7 (368#13))
  | 5 => .base (.ADDI .x24 .x24 (8#12))
  | 6 => .base (.ADDI .x8 .x8 (256#12))
  | 7 => .base (.ADDI .x27 .x27 (4095#12))
  | 8 => .base (.BNE .x27 .x0 (7428#13))
  | 9 => .base (.ADDI .x29 .x2 (480#12))
  | 10 => .base (.ADDI .x30 .x2 (768#12))
  | 11 => .base (.LD .x20 .x29 (8#12))
  | 12 => .base (.LD .x14 .x29 (16#12))
  | 13 => .base (.ADD .x14 .x18 .x14)
  | 14 => .base (.LD .x15 .x29 (48#12))
  | 15 => .base (.ADD .x15 .x18 .x15)
  | 16 => .base (.LD .x16 .x29 (24#12))
  | 17 => .base (.ADD .x16 .x19 .x16)
  | 18 => .base (.LD .x17 .x29 (56#12))
  | 19 => .base (.ADD .x17 .x19 .x17)
  | 20 => .base (.SRLI .x22 .x20 (1#6))
  | 21 => .base (.ADDI .x23 .x0 (0#12))
  | 22 => .base (.SLLI .x6 .x23 (1#6))
  | 23 => .base (.ADD .x6 .x14 .x6)
  | 24 => .base (.LBU .x7 .x6 (0#12))
  | 25 => .base (.LBU .x8 .x6 (1#12))
  | 26 => .base (.OR .x28 .x7 .x8)
  | 27 => .base (.BEQ .x28 .x0 (92#13))
  | 28 => .base (.ADD .x6 .x15 .x23)
  | 29 => .base (.SB .x6 .x28 (0#12))
  | 30 => .base (.SLLI .x6 .x23 (6#6))
  | 31 => .base (.SLLI .x28 .x23 (5#6))
  | 32 => .base (.ADD .x10 .x6 .x28)
  | 33 => .base (.ADD .x10 .x16 .x10)
  | 34 => .base (.BEQ .x7 .x8 (32#13))
  | 35 => .base (.ADDI .x6 .x25 (30#12))
  | 36 => .base (.BLTU .x31 .x6 (240#13))
  | 37 => .base (.ADDI .x12 .x10 (0#12))
  | 38 => .base (.BEQ .x7 .x0 (8#13))
  | 39 => .base (.ADDI .x12 .x10 (32#12))
  | 40 => .base (.JAL .x1 (336#21))
  | 41 => .base (.ADDI .x25 .x25 (30#12))
  | 42 => .base (.SRLI .x6 .x23 (1#6))
  | 43 => .base (.ADD .x6 .x23 .x6)
  | 44 => .base (.SLLI .x6 .x6 (5#6))
  | 45 => .base (.ADD .x12 .x17 .x6)
  | 46 => .base .ECALL
  | 47 => .base (.ADDI .x6 .x2 (736#12))
  | 48 => .base (.BEQ .x29 .x6 (8#13))
  | 49 => .base (.SH .x12 .x0 (30#12))
  | 50 => .base (.ADDI .x23 .x23 (1#12))
  | 51 => .base (.BNE .x23 .x22 (8076#13))
  | 52 => .base (.ANDI .x6 .x20 (1#12))
  | 53 => .base (.BEQ .x6 .x0 (92#13))
  | 54 => .base (.SLLI .x7 .x22 (1#6))
  | 55 => .base (.ADD .x7 .x14 .x7)
  | 56 => .base (.LBU .x8 .x7 (0#12))
  | 57 => .base (.BEQ .x8 .x0 (76#13))
  | 58 => .base (.ADD .x7 .x15 .x22)
  | 59 => .base (.SB .x7 .x8 (0#12))
  | 60 => .base (.SLLI .x6 .x22 (6#6))
  | 61 => .base (.SLLI .x7 .x22 (5#6))
  | 62 => .base (.ADD .x10 .x6 .x7)
  | 63 => .base (.ADD .x10 .x16 .x10)
  | 64 => .base (.SRLI .x6 .x22 (1#6))
  | 65 => .base (.ADD .x6 .x22 .x6)
  | 66 => .base (.SLLI .x6 .x6 (5#6))
  | 67 => .base (.ADD .x12 .x17 .x6)
  | 68 => .base (.LD .x6 .x10 (0#12))
  | 69 => .base (.SD .x12 .x6 (0#12))
  | 70 => .base (.LD .x6 .x10 (8#12))
  | 71 => .base (.SD .x12 .x6 (8#12))
  | 72 => .base (.LD .x6 .x10 (16#12))
  | 73 => .base (.SD .x12 .x6 (16#12))
  | 74 => .base (.LD .x6 .x10 (24#12))
  | 75 => .base (.SD .x12 .x6 (24#12))
  | 76 => .base (.ADDI .x29 .x29 (32#12))
  | 77 => .base (.BNE .x29 .x30 (7928#13))
  | 78 => .base (.BNE .x25 .x31 (72#13))
  | 79 => .base (.LD .x6 .x2 (792#12))
  | 80 => .base (.ADD .x10 .x19 .x6)
  | 81 => .base (.LD .x6 .x10 (0#12))
  | 82 => .base (.LD .x7 .x26 (0#12))
  | 83 => .base (.BNE .x6 .x7 (52#13))
  | 84 => .base (.LD .x6 .x10 (8#12))
  | 85 => .base (.LD .x7 .x26 (8#12))
  | 86 => .base (.BNE .x6 .x7 (40#13))
  | 87 => .base (.LD .x6 .x10 (16#12))
  | 88 => .base (.LD .x7 .x26 (16#12))
  | 89 => .base (.BNE .x6 .x7 (28#13))
  | 90 => .base (.LD .x6 .x10 (24#12))
  | 91 => .base (.LD .x7 .x26 (24#12))
  | 92 => .base (.BNE .x6 .x7 (16#13))
  | 93 => .base (.ADDI .x5 .x0 (1#12))
  | 94 => .base (.ADDI .x10 .x0 (0#12))
  | 95 => .base .ECALL
  | 96 => .base (.ADDI .x5 .x0 (1#12))
  | 97 => .base (.ADDI .x10 .x0 (1#12))
  | 98 => .base .ECALL
  | 99 => .base (.LHU .x6 .x25 (0#12))
  | _ => .base .EBREAK

private def checkInstr3 : Nat → Instruction
  | 0 => .base (.SH .x12 .x6 (0#12))
  | 1 => .base (.LHU .x6 .x25 (2#12))
  | 2 => .base (.SH .x12 .x6 (2#12))
  | 3 => .base (.LHU .x6 .x25 (4#12))
  | 4 => .base (.SH .x12 .x6 (4#12))
  | 5 => .base (.LHU .x6 .x25 (6#12))
  | 6 => .base (.SH .x12 .x6 (6#12))
  | 7 => .base (.LHU .x6 .x25 (8#12))
  | 8 => .base (.SH .x12 .x6 (8#12))
  | 9 => .base (.LHU .x6 .x25 (10#12))
  | 10 => .base (.SH .x12 .x6 (10#12))
  | 11 => .base (.LHU .x6 .x25 (12#12))
  | 12 => .base (.SH .x12 .x6 (12#12))
  | 13 => .base (.LHU .x6 .x25 (14#12))
  | 14 => .base (.SH .x12 .x6 (14#12))
  | 15 => .base (.LHU .x6 .x25 (16#12))
  | 16 => .base (.SH .x12 .x6 (16#12))
  | 17 => .base (.LHU .x6 .x25 (18#12))
  | 18 => .base (.SH .x12 .x6 (18#12))
  | 19 => .base (.LHU .x6 .x25 (20#12))
  | 20 => .base (.SH .x12 .x6 (20#12))
  | 21 => .base (.LHU .x6 .x25 (22#12))
  | 22 => .base (.SH .x12 .x6 (22#12))
  | 23 => .base (.JALR .x0 .x1 (0#12))
  | 24 => .base (.LHU .x6 .x25 (0#12))
  | 25 => .base (.SH .x12 .x6 (0#12))
  | 26 => .base (.LHU .x6 .x25 (2#12))
  | 27 => .base (.SH .x12 .x6 (2#12))
  | 28 => .base (.LHU .x6 .x25 (4#12))
  | 29 => .base (.SH .x12 .x6 (4#12))
  | 30 => .base (.LHU .x6 .x25 (6#12))
  | 31 => .base (.SH .x12 .x6 (6#12))
  | 32 => .base (.LHU .x6 .x25 (8#12))
  | 33 => .base (.SH .x12 .x6 (8#12))
  | 34 => .base (.LHU .x6 .x25 (10#12))
  | 35 => .base (.SH .x12 .x6 (10#12))
  | 36 => .base (.LHU .x6 .x25 (12#12))
  | 37 => .base (.SH .x12 .x6 (12#12))
  | 38 => .base (.LHU .x6 .x25 (14#12))
  | 39 => .base (.SH .x12 .x6 (14#12))
  | 40 => .base (.LHU .x6 .x25 (16#12))
  | 41 => .base (.SH .x12 .x6 (16#12))
  | 42 => .base (.LHU .x6 .x25 (18#12))
  | 43 => .base (.SH .x12 .x6 (18#12))
  | 44 => .base (.LHU .x6 .x25 (20#12))
  | 45 => .base (.SH .x12 .x6 (20#12))
  | 46 => .base (.LHU .x6 .x25 (22#12))
  | 47 => .base (.SH .x12 .x6 (22#12))
  | 48 => .base (.LHU .x6 .x25 (24#12))
  | 49 => .base (.SH .x12 .x6 (24#12))
  | 50 => .base (.LHU .x6 .x25 (26#12))
  | 51 => .base (.SH .x12 .x6 (26#12))
  | 52 => .base (.LHU .x6 .x25 (28#12))
  | 53 => .base (.SH .x12 .x6 (28#12))
  | 54 => .base (.JALR .x0 .x1 (0#12))
  | 55 => .base (.LHU .x6 .x25 (0#12))
  | 56 => .base (.SH .x12 .x6 (0#12))
  | 57 => .base (.LHU .x6 .x25 (2#12))
  | 58 => .base (.SH .x12 .x6 (2#12))
  | 59 => .base (.LHU .x6 .x25 (4#12))
  | 60 => .base (.SH .x12 .x6 (4#12))
  | 61 => .base (.LHU .x6 .x25 (6#12))
  | 62 => .base (.SH .x12 .x6 (6#12))
  | 63 => .base (.LHU .x6 .x25 (8#12))
  | 64 => .base (.SH .x12 .x6 (8#12))
  | 65 => .base (.LHU .x6 .x25 (10#12))
  | 66 => .base (.SH .x12 .x6 (10#12))
  | 67 => .base (.LHU .x6 .x25 (12#12))
  | 68 => .base (.SH .x12 .x6 (12#12))
  | 69 => .base (.LHU .x6 .x25 (14#12))
  | 70 => .base (.SH .x12 .x6 (14#12))
  | 71 => .base (.LHU .x6 .x25 (16#12))
  | 72 => .base (.SH .x12 .x6 (16#12))
  | 73 => .base (.LHU .x6 .x25 (18#12))
  | 74 => .base (.SH .x12 .x6 (18#12))
  | 75 => .base (.LHU .x6 .x25 (20#12))
  | 76 => .base (.SH .x12 .x6 (20#12))
  | 77 => .base (.LHU .x6 .x25 (22#12))
  | 78 => .base (.SH .x12 .x6 (22#12))
  | 79 => .base (.LHU .x6 .x25 (24#12))
  | 80 => .base (.SH .x12 .x6 (24#12))
  | 81 => .base (.LHU .x6 .x25 (26#12))
  | 82 => .base (.SH .x12 .x6 (26#12))
  | 83 => .base (.LHU .x6 .x25 (28#12))
  | 84 => .base (.SH .x12 .x6 (28#12))
  | 85 => .base (.LHU .x6 .x25 (30#12))
  | 86 => .base (.SH .x12 .x6 (30#12))
  | 87 => .base (.JALR .x0 .x1 (0#12))
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

private theorem decode_check_3 (i : Fin 88) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨300 + i.val, by omega⟩) =
      some (checkInstr (300 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 388)
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
