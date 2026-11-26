import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨1879048128, 8239714016⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 6174019552, 6308237280, 10603204576⟩ := rfl

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

/-! ### Commit Program: Parametric Leaf Loop (U = 32, 21 words/lane) -/

def encodeIType (op f3 rd rs1 imm : Nat) : BitVec 32 :=
  let u := imm % 4096
  BitVec.ofNat 32 ((u <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op)

def encodeSType (op f3 rs1 rs2 imm : Nat) : BitVec 32 :=
  let u := imm % 4096
  BitVec.ofNat 32 (((u >>> 5) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| ((u % 32) <<< 7) ||| op)

def encodeRType (op f3 rd rs1 rs2 f7 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((f7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op)

def leafLaneWord (k j : Nat) : BitVec 32 :=
  let soff := (4096 - 256 + 16 * k) % 4096
  let soff8 := (4096 - 248 + 16 * k) % 4096
  let hoff := (4096 - 768 + 32 * (k + k / 2)) % 4096
  match j with
  | 0  => encodeIType 0x13 0 10 10 72
  | 1  => encodeIType 0x03 3 6 18 soff
  | 2  => encodeSType 0x23 3 10 6 0
  | 3  => encodeIType 0x03 3 6 18 soff8
  | 4  => encodeRType 0x33 7 6 6 28 0
  | 5  => encodeSType 0x23 3 10 6 8
  | 6  => encodeSType 0x23 3 10 10 16
  | 7  => encodeIType 0x13 0 12 10 64
  | 8  => 0x00000073#32
  | 9  => encodeIType 0x13 0 10 10 64
  | 10 => encodeIType 0x13 0 12 10 64
  | 11 => 0x00000073#32
  | 12 => encodeIType 0x13 0 10 10 64
  | 13 => encodeIType 0x13 0 12 10 56
  | 14 => 0x00000073#32
  | 15 => encodeIType 0x13 0 10 10 56
  | 16 => encodeIType 0x13 0 12 23 hoff
  | 17 => 0x00000073#32
  | 18 => encodeIType 0x03 3 6 12 24
  | 19 => encodeRType 0x33 7 6 6 27 0
  | 20 => encodeSType 0x23 3 12 6 24
  | _  => 0#32

def leafLaneInstr (k j : Nat) : Instruction :=
  let soff : BitVec 12 := BitVec.ofNat 12 ((4096 - 256 + 16 * k) % 4096)
  let soff8 : BitVec 12 := BitVec.ofNat 12 ((4096 - 248 + 16 * k) % 4096)
  let hoff : BitVec 12 := BitVec.ofNat 12 ((4096 - 768 + 32 * (k + k / 2)) % 4096)
  match j with
  | 0  => .base (.ADDI .x10 .x10 (72#12))
  | 1  => .base (.LD .x6 .x18 soff)
  | 2  => .base (.SD .x10 .x6 (0#12))
  | 3  => .base (.LD .x6 .x18 soff8)
  | 4  => .base (.AND .x6 .x6 .x28)
  | 5  => .base (.SD .x10 .x6 (8#12))
  | 6  => .base (.SD .x10 .x10 (16#12))
  | 7  => .base (.ADDI .x12 .x10 (64#12))
  | 8  => .base .ECALL
  | 9  => .base (.ADDI .x10 .x10 (64#12))
  | 10 => .base (.ADDI .x12 .x10 (64#12))
  | 11 => .base .ECALL
  | 12 => .base (.ADDI .x10 .x10 (64#12))
  | 13 => .base (.ADDI .x12 .x10 (56#12))
  | 14 => .base .ECALL
  | 15 => .base (.ADDI .x10 .x10 (56#12))
  | 16 => .base (.ADDI .x12 .x23 hoff)
  | 17 => .base .ECALL
  | 18 => .base (.LD .x6 .x12 (24#12))
  | 19 => .base (.AND .x6 .x6 .x27)
  | 20 => .base (.SD .x12 .x6 (24#12))
  | _  => .base .EBREAK

theorem decode_leafLaneWord (k : Fin 32) (j : Fin 21) :
    decodeInstruction (leafLaneWord k.val j.val) = some (leafLaneInstr k.val j.val) := by
  fin_cases j <;> (dsimp only; revert k; decide)

private theorem commit_leaf_words_0 (k : Fin 8) (j : Fin 21) :
    MoonArtifact.commitCode.get 32 ⟨26 + 21 * (0 + k.val) + j.val, by omega⟩ =
      leafLaneWord (0 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_1 (k : Fin 8) (j : Fin 21) :
    MoonArtifact.commitCode.get 32 ⟨26 + 21 * (8 + k.val) + j.val, by omega⟩ =
      leafLaneWord (8 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_2 (k : Fin 8) (j : Fin 21) :
    MoonArtifact.commitCode.get 32 ⟨26 + 21 * (16 + k.val) + j.val, by omega⟩ =
      leafLaneWord (16 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_3 (k : Fin 8) (j : Fin 21) :
    MoonArtifact.commitCode.get 32 ⟨26 + 21 * (24 + k.val) + j.val, by omega⟩ =
      leafLaneWord (24 + k.val) j.val := by
  revert k j; decide

theorem commit_fetch_leaf (state : MachineState) (k j : Nat) (hk : k < 32) (hj : j < 21)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + j))) :
    fetch (submission.image .commit) state = some (leafLaneInstr k j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (26 + 21 * k + j) (by omega)
    (leafLaneWord k j) hpc _ (leafLaneInstr k j) (decode_leafLaneWord ⟨k, hk⟩ ⟨j, hj⟩)
  by_cases h0 : k < 8
  · simpa using commit_leaf_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  · by_cases h1 : k < 16
    · have := commit_leaf_words_1 ⟨k - 8, by omega⟩ ⟨j, hj⟩
      simpa [show 8 + (k - 8) = k by omega] using this
    · by_cases h2 : k < 24
      · have := commit_leaf_words_2 ⟨k - 16, by omega⟩ ⟨j, hj⟩
        simpa [show 16 + (k - 16) = k by omega] using this
      · have := commit_leaf_words_3 ⟨k - 24, by omega⟩ ⟨j, hj⟩
        simpa [show 24 + (k - 24) = k by omega] using this

/-! ### Commit Program: Repeating `bin238` Bulk Loop (U = 64, 12 words/pair) -/

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
    MoonArtifact.commitCode.get 32 ⟨716 + 12 * (0 + k.val) + j.val, by omega⟩ = bin238Word j.val := by
  revert k j; decide

private theorem commit_fetch_bin238_words_1 (k : Fin 32) (j : Fin 12) :
    MoonArtifact.commitCode.get 32 ⟨716 + 12 * (32 + k.val) + j.val, by omega⟩ = bin238Word j.val := by
  revert k j; decide

theorem commit_fetch_bin238 (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (716 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (bin238Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (716 + 12 * k + j) (by omega)
    (bin238Word j) hpc _ (bin238Instr j) (decode_bin238Word ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_fetch_bin238_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  · have := commit_fetch_bin238_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
    simpa [show 32 + (k - 32) = k by omega] using this

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x27 .x0 (1#12))
  | 4 => .base (.SLLI .x27 .x27 (46#6))
  | 5 => .base (.ADDI .x27 .x27 (4095#12))
  | 6 => .base (.ADDI .x28 .x0 (1#12))
  | 7 => .base (.SLLI .x28 .x28 (57#6))
  | 8 => .base (.ADDI .x28 .x28 (4095#12))
  | 9 => .base (.ADDI .x6 .x0 (1536#12))
  | 10 => .base (.SLLI .x6 .x6 (20#6))
  | 11 => .base (.ADDI .x6 .x6 (4032#12))
  | 12 => .base (.ADD .x10 .x9 .x6)
  | 13 => .base (.ADDI .x11 .x0 (1#12))
  | 14 => .base (.SLLI .x11 .x11 (28#6))
  | 15 => .base (.ADDI .x5 .x0 (2#12))
  | 16 => .base .ECALL
  | 17 => .base (.ADDI .x18 .x10 (256#12))
  | 18 => .base (.ADDI .x23 .x9 (768#12))
  | 19 => .base (.ADDI .x10 .x8 (4000#12))
  | 20 => .base (.ADDI .x6 .x0 (1#12))
  | 21 => .base (.SLLI .x6 .x6 (32#6))
  | 22 => .base (.ADD .x19 .x10 .x6)
  | 23 => .base (.ADDI .x5 .x0 (0#12))
  | 24 => .base (.ADDI .x11 .x0 (96#12))
  | 25 => .base (.ADDI .x13 .x0 (0#12))
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr (i : Fin 26) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 26)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  have h := decode_commitPrefixInstr ⟨idx - 0, by omega⟩
  have heq : 0 + (idx - 0) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMidInstr : Nat → Instruction
  | 698 => .base (.ADDI .x18 .x18 (512#12))
  | 699 => .base (.ADDI .x23 .x23 (1536#12))
  | 700 => .base (.BNE .x10 .x19 (5496#13))
  | 701 => .base (.ADDI .x24 .x2 (0#12))
  | 702 => .base (.ADDI .x25 .x2 (736#12))
  | 703 => .base (.LD .x6 .x24 (0#12))
  | 704 => .base (.ADD .x10 .x9 .x6)
  | 705 => .base (.ADDI .x10 .x10 (4000#12))
  | 706 => .base (.LD .x6 .x24 (8#12))
  | 707 => .base (.ADD .x12 .x9 .x6)
  | 708 => .base (.ADDI .x12 .x12 (4032#12))
  | 709 => .base (.LD .x20 .x24 (16#12))
  | 710 => .base (.SRLI .x22 .x20 (6#6))
  | 711 => .base (.BEQ .x22 .x0 (3096#13))
  | 712 => .base (.SLLI .x6 .x22 (12#6))
  | 713 => .base (.SLLI .x7 .x22 (13#6))
  | 714 => .base (.ADD .x6 .x6 .x7)
  | 715 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMidInstr (i : Fin 18) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨698 + i.val, by omega⟩) =
      some (commitMidInstr (698 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMidInstr (state : MachineState) (idx : Nat) (hlo : 698 ≤ idx) (hhi : idx < 716)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMidInstr idx) := by
  have h := decode_commitMidInstr ⟨idx - 698, by omega⟩
  have heq : 698 + (idx - 698) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitTailInstr : Nat → Instruction
  | 1484 => .base (.BNE .x10 .x19 (5120#13))
  | 1485 => .base (.ANDI .x22 .x20 (63#12))
  | 1486 => .base (.BEQ .x22 .x0 (60#13))
  | 1487 => .base (.ADDI .x10 .x10 (96#12))
  | 1488 => .base (.ADDI .x12 .x12 (64#12))
  | 1489 => .base .ECALL
  | 1490 => .base (.LD .x6 .x12 (24#12))
  | 1491 => .base (.AND .x6 .x6 .x27)
  | 1492 => .base (.SD .x12 .x6 (24#12))
  | 1493 => .base (.ADDI .x10 .x10 (96#12))
  | 1494 => .base (.ADDI .x12 .x12 (32#12))
  | 1495 => .base .ECALL
  | 1496 => .base (.LD .x6 .x12 (24#12))
  | 1497 => .base (.AND .x6 .x6 .x27)
  | 1498 => .base (.SD .x12 .x6 (24#12))
  | 1499 => .base (.ADDI .x22 .x22 (4095#12))
  | 1500 => .base (.BNE .x22 .x0 (8140#13))
  | 1501 => .base (.ADDI .x24 .x24 (32#12))
  | 1502 => .base (.BNE .x24 .x25 (4996#13))
  | 1503 => .base (.ADDI .x6 .x0 (1536#12))
  | 1504 => .base (.SLLI .x6 .x6 (20#6))
  | 1505 => .base (.ADDI .x6 .x6 (3904#12))
  | 1506 => .base (.ADD .x10 .x9 .x6)
  | 1507 => .base (.ADDI .x6 .x0 (1536#12))
  | 1508 => .base (.SLLI .x6 .x6 (20#6))
  | 1509 => .base (.ADDI .x6 .x6 (4000#12))
  | 1510 => .base (.ADD .x12 .x9 .x6)
  | 1511 => .base .ECALL
  | 1512 => .base (.LD .x6 .x12 (0#12))
  | 1513 => .base (.SD .x26 .x6 (0#12))
  | 1514 => .base (.LD .x6 .x12 (8#12))
  | 1515 => .base (.SD .x26 .x6 (8#12))
  | 1516 => .base (.LD .x6 .x12 (16#12))
  | 1517 => .base (.SD .x26 .x6 (16#12))
  | 1518 => .base (.LD .x6 .x12 (24#12))
  | 1519 => .base (.SD .x26 .x6 (24#12))
  | 1520 => .base (.ADDI .x5 .x0 (1#12))
  | 1521 => .base (.ADDI .x10 .x0 (0#12))
  | 1522 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 39) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨1484 + i.val, by omega⟩) =
      some (commitTailInstr (1484 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 1484 ≤ idx) (hhi : idx < 1523)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 1484, by omega⟩
  have heq : 1484 + (idx - 1484) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

/-! ### Opening Program (203 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (508#13))
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
  | 16 => .base (.ADDI .x6 .x6 (4032#12))
  | 17 => .base (.ADD .x18 .x9 .x6)
  | 18 => .base (.ADDI .x21 .x0 (2#12))
  | 19 => .base (.SLLI .x21 .x21 (11#6))
  | 20 => .base (.ADDI .x28 .x24 (0#12))
  | 21 => .base (.ADDI .x29 .x27 (0#12))
  | 22 => .base (.ADDI .x10 .x0 (0#12))
  | 23 => .base (.ADDI .x11 .x0 (0#12))
  | 24 => .base (.LD .x5 .x28 (0#12))
  | 25 => .base (.SLLI .x5 .x5 (4#6))
  | 26 => .base (.ADD .x5 .x18 .x5)
  | 27 => .base (.LBU .x6 .x5 (15#12))
  | 28 => .base (.ANDI .x6 .x6 (1#12))
  | 29 => .base (.SLL .x6 .x6 .x11)
  | 30 => .base (.OR .x10 .x10 .x6)
  | 31 => .base (.ADDI .x11 .x11 (1#12))
  | 32 => .base (.ADDI .x28 .x28 (8#12))
  | 33 => .base (.ADDI .x29 .x29 (4095#12))
  | 34 => .base (.ADDI .x7 .x0 (8#12))
  | 35 => .base (.BNE .x11 .x7 (48#13))
  | 36 => .base (.SLL .x6 .x10 .x13)
  | 37 => .base (.OR .x12 .x12 .x6)
  | 38 => .base (.ADDI .x13 .x13 (8#12))
  | 39 => .base (.ADDI .x7 .x0 (64#12))
  | 40 => .base (.BNE .x13 .x7 (20#13))
  | 41 => .base (.SD .x25 .x12 (0#12))
  | 42 => .base (.ADDI .x25 .x25 (8#12))
  | 43 => .base (.ADDI .x12 .x0 (0#12))
  | 44 => .base (.ADDI .x13 .x0 (0#12))
  | 45 => .base (.ADDI .x10 .x0 (0#12))
  | 46 => .base (.ADDI .x11 .x0 (0#12))
  | 47 => .base (.BNE .x29 .x0 (8100#13))
  | 48 => .base (.BEQ .x11 .x0 (40#13))
  | 49 => .base (.SLL .x6 .x10 .x13)
  | 50 => .base (.OR .x12 .x12 .x6)
  | 51 => .base (.ADDI .x13 .x13 (8#12))
  | 52 => .base (.ADDI .x7 .x0 (64#12))
  | 53 => .base (.BNE .x13 .x7 (20#13))
  | 54 => .base (.SD .x25 .x12 (0#12))
  | 55 => .base (.ADDI .x25 .x25 (8#12))
  | 56 => .base (.ADDI .x12 .x0 (0#12))
  | 57 => .base (.ADDI .x13 .x0 (0#12))
  | 58 => .base (.XORI .x14 .x13 (63#12))
  | 59 => .base (.LD .x22 .x24 (0#12))
  | 60 => .base (.SLLI .x6 .x22 (4#6))
  | 61 => .base (.ADD .x10 .x18 .x6)
  | 62 => .base (.JAL .x1 (296#21))
  | 63 => .base (.ADDI .x29 .x2 (0#12))
  | 64 => .base (.ADDI .x30 .x2 (512#12))
  | 65 => .base (.XORI .x28 .x22 (1#12))
  | 66 => .base (.SRLI .x6 .x28 (1#6))
  | 67 => .base (.ADD .x28 .x28 .x6)
  | 68 => .base (.SLLI .x28 .x28 (5#6))
  | 69 => .base (.LD .x6 .x29 (0#12))
  | 70 => .base (.ADD .x10 .x9 .x6)
  | 71 => .base (.ADD .x10 .x10 .x28)
  | 72 => .base (.JAL .x1 (344#21))
  | 73 => .base (.SRLI .x22 .x22 (1#6))
  | 74 => .base (.ADDI .x29 .x29 (32#12))
  | 75 => .base (.BNE .x29 .x30 (8152#13))
  | 76 => .base (.ADD .x6 .x21 .x22)
  | 77 => .base (.ADDI .x7 .x0 (1#12))
  | 78 => .base (.SB .x6 .x7 (0#12))
  | 79 => .base (.ADDI .x24 .x24 (8#12))
  | 80 => .base (.ADDI .x27 .x27 (4095#12))
  | 81 => .base (.BNE .x27 .x0 (8104#13))
  | 82 => .base (.ADDI .x29 .x2 (512#12))
  | 83 => .base (.ADDI .x30 .x2 (768#12))
  | 84 => .base (.LD .x18 .x29 (0#12))
  | 85 => .base (.ADD .x18 .x9 .x18)
  | 86 => .base (.LD .x19 .x29 (8#12))
  | 87 => .base (.LD .x20 .x29 (16#12))
  | 88 => .base (.ADD .x20 .x21 .x20)
  | 89 => .base (.LD .x22 .x29 (48#12))
  | 90 => .base (.ADD .x22 .x21 .x22)
  | 91 => .base (.SRLI .x23 .x19 (1#6))
  | 92 => .base (.ADDI .x24 .x0 (0#12))
  | 93 => .base (.SLLI .x6 .x24 (1#6))
  | 94 => .base (.ADD .x6 .x20 .x6)
  | 95 => .base (.LBU .x7 .x6 (0#12))
  | 96 => .base (.LBU .x8 .x6 (1#12))
  | 97 => .base (.OR .x11 .x7 .x8)
  | 98 => .base (.ADD .x6 .x22 .x24)
  | 99 => .base (.SB .x6 .x11 (0#12))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.BEQ .x7 .x8 (32#13))
  | 1 => .base (.SLLI .x6 .x24 (6#6))
  | 2 => .base (.SLLI .x11 .x24 (5#6))
  | 3 => .base (.ADD .x10 .x6 .x11)
  | 4 => .base (.ADD .x10 .x18 .x10)
  | 5 => .base (.BEQ .x7 .x0 (8#13))
  | 6 => .base (.ADDI .x10 .x10 (32#12))
  | 7 => .base (.JAL .x1 (204#21))
  | 8 => .base (.ADDI .x24 .x24 (1#12))
  | 9 => .base (.BNE .x24 .x23 (8128#13))
  | 10 => .base (.ADDI .x29 .x29 (32#12))
  | 11 => .base (.BNE .x29 .x30 (8084#13))
  | 12 => .base (.ADDI .x10 .x25 (0#12))
  | 13 => .base (.BEQ .x13 .x0 (24#13))
  | 14 => .base (.SB .x10 .x12 (0#12))
  | 15 => .base (.ADDI .x10 .x10 (1#12))
  | 16 => .base (.SRLI .x12 .x12 (8#6))
  | 17 => .base (.ADDI .x13 .x13 (4088#12))
  | 18 => .base (.BNE .x13 .x0 (8176#13))
  | 19 => .base (.BEQ .x17 .x0 (12#13))
  | 20 => .base (.SB .x15 .x16 (0#12))
  | 21 => .base (.ADDI .x15 .x15 (1#12))
  | 22 => .base (.BEQ .x15 .x31 (24#13))
  | 23 => .base (.ADDI .x15 .x15 (4095#12))
  | 24 => .base (.LBU .x6 .x15 (0#12))
  | 25 => .base (.SB .x10 .x6 (0#12))
  | 26 => .base (.ADDI .x10 .x10 (1#12))
  | 27 => .base (.BNE .x15 .x31 (8176#13))
  | 28 => .base (.SUB .x11 .x10 .x26)
  | 29 => .base (.ADDI .x5 .x0 (1#12))
  | 30 => .base (.ADDI .x10 .x0 (0#12))
  | 31 => .base .ECALL
  | 32 => .base (.ADDI .x11 .x0 (0#12))
  | 33 => .base (.ADDI .x5 .x0 (1#12))
  | 34 => .base (.ADDI .x10 .x0 (0#12))
  | 35 => .base .ECALL
  | 36 => .base (.LD .x5 .x10 (0#12))
  | 37 => .base (.SLL .x6 .x5 .x13)
  | 38 => .base (.OR .x12 .x12 .x6)
  | 39 => .base (.SD .x25 .x12 (0#12))
  | 40 => .base (.SRLI .x5 .x5 (1#6))
  | 41 => .base (.SRL .x12 .x5 .x14)
  | 42 => .base (.ADDI .x25 .x25 (8#12))
  | 43 => .base (.LD .x5 .x10 (8#12))
  | 44 => .base (.SLLI .x5 .x5 (8#6))
  | 45 => .base (.SRLI .x5 .x5 (8#6))
  | 46 => .base (.SLL .x6 .x5 .x13)
  | 47 => .base (.OR .x12 .x12 .x6)
  | 48 => .base (.ADDI .x13 .x13 (56#12))
  | 49 => .base (.ADDI .x7 .x0 (64#12))
  | 50 => .base (.BLTU .x13 .x7 (24#13))
  | 51 => .base (.SD .x25 .x12 (0#12))
  | 52 => .base (.ADDI .x25 .x25 (8#12))
  | 53 => .base (.SRLI .x5 .x5 (1#6))
  | 54 => .base (.SRL .x12 .x5 .x14)
  | 55 => .base (.ADDI .x13 .x13 (4032#12))
  | 56 => .base (.XORI .x14 .x13 (63#12))
  | 57 => .base (.JALR .x0 .x1 (0#12))
  | 58 => .base (.LD .x5 .x10 (0#12))
  | 59 => .base (.SLL .x6 .x5 .x13)
  | 60 => .base (.OR .x12 .x12 .x6)
  | 61 => .base (.SD .x25 .x12 (0#12))
  | 62 => .base (.SRLI .x5 .x5 (1#6))
  | 63 => .base (.SRL .x12 .x5 .x14)
  | 64 => .base (.LD .x5 .x10 (8#12))
  | 65 => .base (.SLL .x6 .x5 .x13)
  | 66 => .base (.OR .x12 .x12 .x6)
  | 67 => .base (.SD .x25 .x12 (8#12))
  | 68 => .base (.SRLI .x5 .x5 (1#6))
  | 69 => .base (.SRL .x12 .x5 .x14)
  | 70 => .base (.LD .x5 .x10 (16#12))
  | 71 => .base (.SLL .x6 .x5 .x13)
  | 72 => .base (.OR .x12 .x12 .x6)
  | 73 => .base (.SD .x25 .x12 (16#12))
  | 74 => .base (.SRLI .x5 .x5 (1#6))
  | 75 => .base (.SRL .x12 .x5 .x14)
  | 76 => .base (.ADDI .x25 .x25 (24#12))
  | 77 => .base (.LD .x11 .x10 (24#12))
  | 78 => .base (.SLLI .x5 .x11 (24#6))
  | 79 => .base (.SRLI .x5 .x5 (24#6))
  | 80 => .base (.SLL .x6 .x5 .x13)
  | 81 => .base (.OR .x12 .x12 .x6)
  | 82 => .base (.ADDI .x13 .x13 (40#12))
  | 83 => .base (.ADDI .x7 .x0 (64#12))
  | 84 => .base (.BLTU .x13 .x7 (24#13))
  | 85 => .base (.SD .x25 .x12 (0#12))
  | 86 => .base (.ADDI .x25 .x25 (8#12))
  | 87 => .base (.SRLI .x5 .x5 (1#6))
  | 88 => .base (.SRL .x12 .x5 .x14)
  | 89 => .base (.ADDI .x13 .x13 (4032#12))
  | 90 => .base (.XORI .x14 .x13 (63#12))
  | 91 => .base (.SRLI .x5 .x11 (40#6))
  | 92 => .base (.ANDI .x5 .x5 (63#12))
  | 93 => .base (.SLL .x6 .x5 .x17)
  | 94 => .base (.OR .x16 .x16 .x6)
  | 95 => .base (.ADDI .x17 .x17 (6#12))
  | 96 => .base (.ADDI .x7 .x0 (8#12))
  | 97 => .base (.BLTU .x17 .x7 (20#13))
  | 98 => .base (.SB .x15 .x16 (0#12))
  | 99 => .base (.ADDI .x15 .x15 (1#12))
  | _ => .base .EBREAK

private def openingInstr2 : Nat → Instruction
  | 0 => .base (.SRLI .x16 .x16 (8#6))
  | 1 => .base (.ADDI .x17 .x17 (4088#12))
  | 2 => .base (.JALR .x0 .x1 (0#12))
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

private theorem decode_opening_2 (i : Fin 3) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (openingInstr (200 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 203)
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

/-! ### Check Program (295 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (1016#13))
  | 8 => .base (.JAL .x0 (1000#21))
  | 9 => .base (.ADDI .x14 .x25 (0#12))
  | 10 => .base (.ADDI .x15 .x0 (0#12))
  | 11 => .base (.ADDI .x6 .x27 (7#12))
  | 12 => .base (.SRLI .x6 .x6 (3#6))
  | 13 => .base (.ADD .x6 .x25 .x6)
  | 14 => .base (.BLTU .x31 .x6 (988#13))
  | 15 => .base (.ANDI .x7 .x27 (7#12))
  | 16 => .base (.BEQ .x7 .x0 (16#13))
  | 17 => .base (.LBU .x5 .x6 (4095#12))
  | 18 => .base (.SRL .x5 .x5 .x7)
  | 19 => .base (.BNE .x5 .x0 (968#13))
  | 20 => .base (.ADDI .x25 .x6 (0#12))
  | 21 => .base (.ADDI .x3 .x0 (0#12))
  | 22 => .base (.ADDI .x4 .x0 (0#12))
  | 23 => .base (.ADDI .x9 .x0 (1#12))
  | 24 => .base (.SLLI .x9 .x9 (46#6))
  | 25 => .base (.ADDI .x9 .x9 (4095#12))
  | 26 => .base (.ADDI .x21 .x0 (256#12))
  | 27 => .base (.ADDI .x18 .x0 (2#12))
  | 28 => .base (.SLLI .x18 .x18 (11#6))
  | 29 => .base (.ADDI .x19 .x0 (4#12))
  | 30 => .base (.SLLI .x19 .x19 (11#6))
  | 31 => .base (.ADDI .x5 .x0 (0#12))
  | 32 => .base (.ADDI .x11 .x0 (96#12))
  | 33 => .base (.ADDI .x13 .x0 (0#12))
  | 34 => .base (.LD .x20 .x24 (0#12))
  | 35 => .base (.ADDI .x6 .x25 (15#12))
  | 36 => .base (.BLTU .x31 .x6 (900#13))
  | 37 => .base (.ADDI .x12 .x21 (0#12))
  | 38 => .base (.ADDI .x10 .x0 (15#12))
  | 39 => .base (.JAL .x1 (900#21))
  | 40 => .base (.SRLI .x6 .x15 (3#6))
  | 41 => .base (.ADD .x6 .x14 .x6)
  | 42 => .base (.LBU .x6 .x6 (0#12))
  | 43 => .base (.ANDI .x7 .x15 (7#12))
  | 44 => .base (.SRL .x6 .x6 .x7)
  | 45 => .base (.ANDI .x6 .x6 (1#12))
  | 46 => .base (.SB .x21 .x6 (15#12))
  | 47 => .base (.SLLI .x6 .x20 (8#6))
  | 48 => .base (.ADDI .x6 .x6 (2036#12))
  | 49 => .base (.ADDI .x6 .x6 (2036#12))
  | 50 => .base (.SD .x21 .x6 (16#12))
  | 51 => .base (.LD .x6 .x8 (0#12))
  | 52 => .base (.SD .x21 .x6 (24#12))
  | 53 => .base (.LD .x6 .x8 (8#12))
  | 54 => .base (.SD .x21 .x6 (32#12))
  | 55 => .base (.LD .x6 .x8 (16#12))
  | 56 => .base (.SD .x21 .x6 (40#12))
  | 57 => .base (.LD .x6 .x8 (24#12))
  | 58 => .base (.SD .x21 .x6 (48#12))
  | 59 => .base (.LD .x6 .x8 (32#12))
  | 60 => .base (.SD .x21 .x6 (56#12))
  | 61 => .base (.LD .x6 .x8 (40#12))
  | 62 => .base (.SD .x21 .x6 (64#12))
  | 63 => .base (.LD .x6 .x8 (48#12))
  | 64 => .base (.SD .x21 .x6 (72#12))
  | 65 => .base (.LD .x6 .x8 (56#12))
  | 66 => .base (.SD .x21 .x6 (80#12))
  | 67 => .base (.LD .x6 .x8 (64#12))
  | 68 => .base (.SD .x21 .x6 (88#12))
  | 69 => .base (.ADDI .x10 .x21 (0#12))
  | 70 => .base (.ADDI .x12 .x21 (0#12))
  | 71 => .base .ECALL
  | 72 => .base (.LD .x6 .x8 (72#12))
  | 73 => .base (.SD .x21 .x6 (32#12))
  | 74 => .base (.LD .x6 .x8 (80#12))
  | 75 => .base (.SD .x21 .x6 (40#12))
  | 76 => .base (.LD .x6 .x8 (88#12))
  | 77 => .base (.SD .x21 .x6 (48#12))
  | 78 => .base (.LD .x6 .x8 (96#12))
  | 79 => .base (.SD .x21 .x6 (56#12))
  | 80 => .base (.LD .x6 .x8 (104#12))
  | 81 => .base (.SD .x21 .x6 (64#12))
  | 82 => .base (.LD .x6 .x8 (112#12))
  | 83 => .base (.SD .x21 .x6 (72#12))
  | 84 => .base (.LD .x6 .x8 (120#12))
  | 85 => .base (.SD .x21 .x6 (80#12))
  | 86 => .base (.LD .x6 .x8 (128#12))
  | 87 => .base (.SD .x21 .x6 (88#12))
  | 88 => .base (.ADDI .x10 .x21 (0#12))
  | 89 => .base (.ADDI .x12 .x21 (0#12))
  | 90 => .base .ECALL
  | 91 => .base (.LD .x6 .x8 (136#12))
  | 92 => .base (.SD .x21 .x6 (32#12))
  | 93 => .base (.LD .x6 .x8 (144#12))
  | 94 => .base (.SD .x21 .x6 (40#12))
  | 95 => .base (.LD .x6 .x8 (152#12))
  | 96 => .base (.SD .x21 .x6 (48#12))
  | 97 => .base (.LD .x6 .x8 (160#12))
  | 98 => .base (.SD .x21 .x6 (56#12))
  | 99 => .base (.LD .x6 .x8 (168#12))
  | _ => .base .EBREAK

private def checkInstr1 : Nat → Instruction
  | 0 => .base (.SD .x21 .x6 (64#12))
  | 1 => .base (.LD .x6 .x8 (176#12))
  | 2 => .base (.SD .x21 .x6 (72#12))
  | 3 => .base (.LD .x6 .x8 (184#12))
  | 4 => .base (.SD .x21 .x6 (80#12))
  | 5 => .base (.LD .x6 .x8 (192#12))
  | 6 => .base (.SD .x21 .x6 (88#12))
  | 7 => .base (.ADDI .x10 .x21 (0#12))
  | 8 => .base (.ADDI .x12 .x21 (0#12))
  | 9 => .base .ECALL
  | 10 => .base (.LD .x6 .x8 (192#12))
  | 11 => .base (.SD .x21 .x6 (32#12))
  | 12 => .base (.LD .x6 .x8 (200#12))
  | 13 => .base (.SD .x21 .x6 (40#12))
  | 14 => .base (.LD .x6 .x8 (208#12))
  | 15 => .base (.SD .x21 .x6 (48#12))
  | 16 => .base (.LD .x6 .x8 (216#12))
  | 17 => .base (.SD .x21 .x6 (56#12))
  | 18 => .base (.LD .x6 .x8 (224#12))
  | 19 => .base (.SD .x21 .x6 (64#12))
  | 20 => .base (.LD .x6 .x8 (232#12))
  | 21 => .base (.SD .x21 .x6 (72#12))
  | 22 => .base (.LD .x6 .x8 (240#12))
  | 23 => .base (.SD .x21 .x6 (80#12))
  | 24 => .base (.LD .x6 .x8 (248#12))
  | 25 => .base (.SD .x21 .x6 (88#12))
  | 26 => .base (.ADDI .x10 .x21 (0#12))
  | 27 => .base (.ADDI .x12 .x21 (0#12))
  | 28 => .base .ECALL
  | 29 => .base (.LD .x6 .x21 (24#12))
  | 30 => .base (.AND .x6 .x6 .x9)
  | 31 => .base (.SD .x21 .x6 (24#12))
  | 32 => .base (.SD .x21 .x0 (64#12))
  | 33 => .base (.SD .x21 .x0 (72#12))
  | 34 => .base (.SD .x21 .x0 (80#12))
  | 35 => .base (.SD .x21 .x0 (88#12))
  | 36 => .base (.ADDI .x22 .x20 (0#12))
  | 37 => .base (.ADDI .x29 .x2 (0#12))
  | 38 => .base (.ADDI .x30 .x2 (512#12))
  | 39 => .base (.ANDI .x7 .x22 (1#12))
  | 40 => .base (.BEQ .x7 .x0 (48#13))
  | 41 => .base (.LD .x6 .x21 (0#12))
  | 42 => .base (.SD .x21 .x6 (32#12))
  | 43 => .base (.LD .x6 .x21 (8#12))
  | 44 => .base (.SD .x21 .x6 (40#12))
  | 45 => .base (.LD .x6 .x21 (16#12))
  | 46 => .base (.SD .x21 .x6 (48#12))
  | 47 => .base (.LD .x6 .x21 (24#12))
  | 48 => .base (.SD .x21 .x6 (56#12))
  | 49 => .base (.ADDI .x12 .x21 (0#12))
  | 50 => .base (.JAL .x1 (484#21))
  | 51 => .base (.JAL .x0 (12#21))
  | 52 => .base (.ADDI .x12 .x21 (32#12))
  | 53 => .base (.JAL .x1 (472#21))
  | 54 => .base (.ADDI .x10 .x21 (0#12))
  | 55 => .base (.ADDI .x12 .x21 (0#12))
  | 56 => .base .ECALL
  | 57 => .base (.LD .x6 .x21 (24#12))
  | 58 => .base (.AND .x6 .x6 .x9)
  | 59 => .base (.SD .x21 .x6 (24#12))
  | 60 => .base (.SRLI .x22 .x22 (1#6))
  | 61 => .base (.ADDI .x29 .x29 (32#12))
  | 62 => .base (.BNE .x29 .x30 (8100#13))
  | 63 => .base (.SRLI .x6 .x22 (1#6))
  | 64 => .base (.ADD .x6 .x22 .x6)
  | 65 => .base (.SLLI .x6 .x6 (5#6))
  | 66 => .base (.ADD .x28 .x19 .x6)
  | 67 => .base (.ADD .x29 .x18 .x22)
  | 68 => .base (.LBU .x7 .x29 (0#12))
  | 69 => .base (.BNE .x7 .x0 (48#13))
  | 70 => .base (.ADDI .x7 .x0 (1#12))
  | 71 => .base (.SB .x29 .x7 (0#12))
  | 72 => .base (.LD .x6 .x21 (0#12))
  | 73 => .base (.SD .x28 .x6 (0#12))
  | 74 => .base (.LD .x6 .x21 (8#12))
  | 75 => .base (.SD .x28 .x6 (8#12))
  | 76 => .base (.LD .x6 .x21 (16#12))
  | 77 => .base (.SD .x28 .x6 (16#12))
  | 78 => .base (.LD .x6 .x21 (24#12))
  | 79 => .base (.SD .x28 .x6 (24#12))
  | 80 => .base (.JAL .x0 (52#21))
  | 81 => .base (.LD .x6 .x21 (0#12))
  | 82 => .base (.LD .x7 .x28 (0#12))
  | 83 => .base (.BNE .x6 .x7 (312#13))
  | 84 => .base (.LD .x6 .x21 (8#12))
  | 85 => .base (.LD .x7 .x28 (8#12))
  | 86 => .base (.BNE .x6 .x7 (300#13))
  | 87 => .base (.LD .x6 .x21 (16#12))
  | 88 => .base (.LD .x7 .x28 (16#12))
  | 89 => .base (.BNE .x6 .x7 (288#13))
  | 90 => .base (.LD .x6 .x21 (24#12))
  | 91 => .base (.LD .x7 .x28 (24#12))
  | 92 => .base (.BNE .x6 .x7 (276#13))
  | 93 => .base (.ADDI .x24 .x24 (8#12))
  | 94 => .base (.ADDI .x8 .x8 (256#12))
  | 95 => .base (.ADDI .x15 .x15 (1#12))
  | 96 => .base (.ADDI .x27 .x27 (4095#12))
  | 97 => .base (.BNE .x27 .x0 (7540#13))
  | 98 => .base (.ADDI .x29 .x2 (512#12))
  | 99 => .base (.ADDI .x30 .x2 (768#12))
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.LD .x20 .x29 (8#12))
  | 1 => .base (.LD .x14 .x29 (16#12))
  | 2 => .base (.ADD .x14 .x18 .x14)
  | 3 => .base (.LD .x15 .x29 (48#12))
  | 4 => .base (.ADD .x15 .x18 .x15)
  | 5 => .base (.LD .x16 .x29 (24#12))
  | 6 => .base (.ADD .x16 .x19 .x16)
  | 7 => .base (.LD .x17 .x29 (56#12))
  | 8 => .base (.ADD .x17 .x19 .x17)
  | 9 => .base (.SRLI .x22 .x20 (1#6))
  | 10 => .base (.ADDI .x23 .x0 (0#12))
  | 11 => .base (.SLLI .x6 .x23 (1#6))
  | 12 => .base (.ADD .x6 .x14 .x6)
  | 13 => .base (.LBU .x7 .x6 (0#12))
  | 14 => .base (.LBU .x8 .x6 (1#12))
  | 15 => .base (.OR .x28 .x7 .x8)
  | 16 => .base (.BEQ .x28 .x0 (88#13))
  | 17 => .base (.ADD .x6 .x15 .x23)
  | 18 => .base (.SB .x6 .x28 (0#12))
  | 19 => .base (.SLLI .x6 .x23 (6#6))
  | 20 => .base (.SLLI .x28 .x23 (5#6))
  | 21 => .base (.ADD .x10 .x6 .x28)
  | 22 => .base (.ADD .x10 .x16 .x10)
  | 23 => .base (.BEQ .x7 .x8 (20#13))
  | 24 => .base (.ADDI .x12 .x10 (0#12))
  | 25 => .base (.BEQ .x7 .x0 (8#13))
  | 26 => .base (.ADDI .x12 .x10 (32#12))
  | 27 => .base (.JAL .x1 (176#21))
  | 28 => .base (.SRLI .x6 .x23 (1#6))
  | 29 => .base (.ADD .x6 .x23 .x6)
  | 30 => .base (.SLLI .x6 .x6 (5#6))
  | 31 => .base (.ADD .x12 .x17 .x6)
  | 32 => .base .ECALL
  | 33 => .base (.ADDI .x6 .x2 (736#12))
  | 34 => .base (.BEQ .x29 .x6 (16#13))
  | 35 => .base (.LD .x6 .x12 (24#12))
  | 36 => .base (.AND .x6 .x6 .x9)
  | 37 => .base (.SD .x12 .x6 (24#12))
  | 38 => .base (.ADDI .x23 .x23 (1#12))
  | 39 => .base (.BNE .x23 .x22 (8080#13))
  | 40 => .base (.ADDI .x29 .x29 (32#12))
  | 41 => .base (.BNE .x29 .x30 (8028#13))
  | 42 => .base (.BNE .x25 .x31 (76#13))
  | 43 => .base (.BNE .x3 .x0 (72#13))
  | 44 => .base (.LD .x6 .x2 (792#12))
  | 45 => .base (.ADD .x10 .x19 .x6)
  | 46 => .base (.LD .x6 .x10 (0#12))
  | 47 => .base (.LD .x7 .x26 (0#12))
  | 48 => .base (.BNE .x6 .x7 (52#13))
  | 49 => .base (.LD .x6 .x10 (8#12))
  | 50 => .base (.LD .x7 .x26 (8#12))
  | 51 => .base (.BNE .x6 .x7 (40#13))
  | 52 => .base (.LD .x6 .x10 (16#12))
  | 53 => .base (.LD .x7 .x26 (16#12))
  | 54 => .base (.BNE .x6 .x7 (28#13))
  | 55 => .base (.LD .x6 .x10 (24#12))
  | 56 => .base (.LD .x7 .x26 (24#12))
  | 57 => .base (.BNE .x6 .x7 (16#13))
  | 58 => .base (.ADDI .x5 .x0 (1#12))
  | 59 => .base (.ADDI .x10 .x0 (0#12))
  | 60 => .base .ECALL
  | 61 => .base (.ADDI .x5 .x0 (1#12))
  | 62 => .base (.ADDI .x10 .x0 (1#12))
  | 63 => .base .ECALL
  | 64 => .base (.LBU .x6 .x25 (0#12))
  | 65 => .base (.SB .x12 .x6 (0#12))
  | 66 => .base (.ADDI .x25 .x25 (1#12))
  | 67 => .base (.ADDI .x12 .x12 (1#12))
  | 68 => .base (.ADDI .x10 .x10 (4095#12))
  | 69 => .base (.BNE .x10 .x0 (8172#13))
  | 70 => .base (.JALR .x0 .x1 (0#12))
  | 71 => .base (.ADDI .x6 .x25 (29#12))
  | 72 => .base (.BLTU .x31 .x6 (8148#13))
  | 73 => .base (.ADDI .x7 .x0 (29#12))
  | 74 => .base (.LBU .x6 .x25 (0#12))
  | 75 => .base (.SB .x12 .x6 (0#12))
  | 76 => .base (.ADDI .x25 .x25 (1#12))
  | 77 => .base (.ADDI .x12 .x12 (1#12))
  | 78 => .base (.ADDI .x7 .x7 (4095#12))
  | 79 => .base (.BNE .x7 .x0 (8172#13))
  | 80 => .base (.ADDI .x7 .x0 (6#12))
  | 81 => .base (.BGEU .x4 .x7 (28#13))
  | 82 => .base (.BGEU .x25 .x31 (8108#13))
  | 83 => .base (.ADDI .x31 .x31 (4095#12))
  | 84 => .base (.LBU .x6 .x31 (0#12))
  | 85 => .base (.SLL .x6 .x6 .x4)
  | 86 => .base (.OR .x3 .x3 .x6)
  | 87 => .base (.ADDI .x4 .x4 (8#12))
  | 88 => .base (.ANDI .x6 .x3 (63#12))
  | 89 => .base (.SRLI .x3 .x3 (6#6))
  | 90 => .base (.ADDI .x4 .x4 (4090#12))
  | 91 => .base (.SB .x12 .x6 (0#12))
  | 92 => .base (.SB .x12 .x0 (1#12))
  | 93 => .base (.SB .x12 .x0 (2#12))
  | 94 => .base (.JALR .x0 .x1 (0#12))
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

private theorem decode_check_2 (i : Fin 95) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (checkInstr (200 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 295)
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
