import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Never unfolds `List.ofFn`; all lookups index directly into `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨1342178336, 8422172696⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 5637149760, 5771367488, 10066334784⟩ := rfl

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

/-! ### Commit Program: Parametric Bulk Encodings + Non-Parametric Slices -/

def encodeIType (op f3 rd rs1 imm : Nat) : BitVec 32 :=
  let u := imm % 4096
  BitVec.ofNat 32 ((u <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| op)

def encodeSType (op f3 rs1 rs2 imm : Nat) : BitVec 32 :=
  let u := imm % 4096
  BitVec.ofNat 32 (((u >>> 5) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| ((u % 32) <<< 7) ||| op)

def leafLaneWord (k j : Nat) : BitVec 32 :=
  let soff := (4096 - 1024 + 16 * k) % 4096
  let hoff := (4096 - 2048 + 32 * k) % 4096
  match j with
  | 0  => encodeIType 0x13 0 10 10 72
  | 1  => encodeIType 0x03 3 6 18 soff
  | 2  => encodeSType 0x23 3 10 6 0
  | 3  => encodeIType 0x03 3 6 18 ((soff + 8) % 4096)
  | 4  => encodeSType 0x23 3 10 6 8
  | 5  => encodeSType 0x23 3 10 10 16
  | 6  => encodeIType 0x13 0 12 10 64
  | 7  => 0x00000073#32
  | 8  => encodeIType 0x13 0 10 10 64
  | 9  => encodeIType 0x13 0 12 10 64
  | 10 => 0x00000073#32
  | 11 => encodeIType 0x13 0 10 10 64
  | 12 => encodeIType 0x13 0 12 10 56
  | 13 => 0x00000073#32
  | 14 => encodeIType 0x13 0 10 10 56
  | 15 => encodeIType 0x13 0 12 23 hoff
  | 16 => 0x00000073#32
  | _  => 0#32

def leafLaneInstr (k j : Nat) : Instruction :=
  let soff : BitVec 12 := BitVec.ofNat 12 ((4096 - 1024 + 16 * k) % 4096)
  let soff8 : BitVec 12 := BitVec.ofNat 12 ((4096 - 1016 + 16 * k) % 4096)
  let hoff : BitVec 12 := BitVec.ofNat 12 ((4096 - 2048 + 32 * k) % 4096)
  match j with
  | 0  => .base (.ADDI .x10 .x10 (72#12))
  | 1  => .base (.LD .x6 .x18 soff)
  | 2  => .base (.SD .x10 .x6 (0#12))
  | 3  => .base (.LD .x6 .x18 soff8)
  | 4  => .base (.SD .x10 .x6 (8#12))
  | 5  => .base (.SD .x10 .x10 (16#12))
  | 6  => .base (.ADDI .x12 .x10 (64#12))
  | 7  => .base .ECALL
  | 8  => .base (.ADDI .x10 .x10 (64#12))
  | 9  => .base (.ADDI .x12 .x10 (64#12))
  | 10 => .base .ECALL
  | 11 => .base (.ADDI .x10 .x10 (64#12))
  | 12 => .base (.ADDI .x12 .x10 (56#12))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x10 .x10 (56#12))
  | 15 => .base (.ADDI .x12 .x23 hoff)
  | 16 => .base .ECALL
  | _  => .base .EBREAK

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

theorem decode_leafLaneWord (k : Fin 128) (j : Fin 17) :
    decodeInstruction (leafLaneWord k.val j.val) = some (leafLaneInstr k.val j.val) := by
  fin_cases j <;> (dsimp only; revert k; decide)

private theorem commit_leaf_words_0 (k : Fin 32) (j : Fin 17) :
    MoonArtifact.commitCode.get 32 ⟨29 + 17 * (0 + k.val) + j.val, by omega⟩ =
      leafLaneWord (0 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_1 (k : Fin 32) (j : Fin 17) :
    MoonArtifact.commitCode.get 32 ⟨29 + 17 * (32 + k.val) + j.val, by omega⟩ =
      leafLaneWord (32 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_2 (k : Fin 32) (j : Fin 17) :
    MoonArtifact.commitCode.get 32 ⟨29 + 17 * (64 + k.val) + j.val, by omega⟩ =
      leafLaneWord (64 + k.val) j.val := by
  revert k j; decide

private theorem commit_leaf_words_3 (k : Fin 32) (j : Fin 17) :
    MoonArtifact.commitCode.get 32 ⟨29 + 17 * (96 + k.val) + j.val, by omega⟩ =
      leafLaneWord (96 + k.val) j.val := by
  revert k j; decide

theorem commit_fetch_leaf (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 17)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + j))) :
    fetch (submission.image .commit) state = some (leafLaneInstr k j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (29 + 17 * k + j) (by omega)
    (leafLaneWord k j) hpc _ (leafLaneInstr k j) (decode_leafLaneWord ⟨k, hk⟩ ⟨j, hj⟩)
  by_cases h0 : k < 32
  · simpa using commit_leaf_words_0 ⟨k, h0⟩ ⟨j, hj⟩
  · by_cases h1 : k < 64
    · have := commit_leaf_words_1 ⟨k - 32, by omega⟩ ⟨j, hj⟩
      simpa [show 32 + (k - 32) = k by omega] using this
    · by_cases h2 : k < 96
      · have := commit_leaf_words_2 ⟨k - 64, by omega⟩ ⟨j, hj⟩
        simpa [show 64 + (k - 64) = k by omega] using this
      · have := commit_leaf_words_3 ⟨k - 96, by omega⟩ ⟨j, hj⟩
        simpa [show 96 + (k - 96) = k by omega] using this

def l1PairWord : Nat → BitVec 32
  | 0 => encodeIType 0x13 0 10 10 96
  | 1 => encodeIType 0x13 0 12 12 64
  | 2 => 0x00000073#32
  | 3 => encodeIType 0x13 0 10 10 96
  | 4 => encodeIType 0x13 0 12 12 32
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

private theorem commit_l1_bulk_words (p : Fin 64) (j : Fin 6) :
    MoonArtifact.commitCode.get 32 ⟨2221 + 6 * p.val + j.val, by omega⟩ = l1PairWord j.val := by
  revert p j; decide

theorem commit_fetch_l1_bulk (state : MachineState) (p j : Nat) (hp : p < 64) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (2221 + 6 * p + j))) :
    fetch (submission.image .commit) state = some (l1PairInstr j) :=
  fetch_of_packed_word MoonArtifact.commitCode _ state (2221 + 6 * p + j) (by omega)
    (l1PairWord j) hpc (commit_l1_bulk_words ⟨p, hp⟩ ⟨j, hj⟩) (l1PairInstr j)
    (decode_l1PairWord ⟨j, hj⟩)

def binPairWord : Nat → BitVec 32
  | 0 => encodeIType 0x13 0 10 10 96
  | 1 => encodeIType 0x13 0 12 12 64
  | 2 => 0x00000073#32
  | 3 => encodeSType 0x23 1 12 0 30
  | 4 => encodeIType 0x13 0 10 10 96
  | 5 => encodeIType 0x13 0 12 12 32
  | 6 => 0x00000073#32
  | 7 => encodeSType 0x23 1 12 0 30
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

private theorem commit_bin_bulk_words (p : Fin 64) (j : Fin 8) :
    MoonArtifact.commitCode.get 32 ⟨2646 + 8 * p.val + j.val, by omega⟩ = binPairWord j.val := by
  revert p j; decide

theorem commit_fetch_bin_bulk (state : MachineState) (p j : Nat) (hp : p < 64) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (2646 + 8 * p + j))) :
    fetch (submission.image .commit) state = some (binPairInstr j) :=
  fetch_of_packed_word MoonArtifact.commitCode _ state (2646 + 8 * p + j) (by omega)
    (binPairWord j) hpc (commit_bin_bulk_words ⟨p, hp⟩ ⟨j, hj⟩) (binPairInstr j)
    (decode_binPairWord ⟨j, hj⟩)

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
  | 9 => .base (.ADDI .x10 .x18 (0#12))
  | 10 => .base (.ADDI .x11 .x0 (64#12))
  | 11 => .base (.SLLI .x11 .x11 (11#6))
  | 12 => .base (.SLLI .x11 .x11 (11#6))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x10 .x8 (4000#12))
  | 15 => .base (.ADDI .x19 .x0 (1024#12))
  | 16 => .base (.SLLI .x19 .x19 (11#6))
  | 17 => .base (.ADDI .x19 .x19 (1#12))
  | 18 => .base (.SLLI .x19 .x19 (11#6))
  | 19 => .base (.ADDI .x19 .x19 (1952#12))
  | 20 => .base (.ADDI .x20 .x0 (2#12))
  | 21 => .base (.SLLI .x20 .x20 (11#6))
  | 22 => .base (.ADDI .x21 .x0 (1#12))
  | 23 => .base (.SLLI .x21 .x21 (11#6))
  | 24 => .base (.ADDI .x18 .x18 (1024#12))
  | 25 => .base (.ADD .x23 .x9 .x21)
  | 26 => .base (.ADDI .x5 .x0 (0#12))
  | 27 => .base (.ADDI .x11 .x0 (96#12))
  | 28 => .base (.ADDI .x13 .x0 (0#12))
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr (i : Fin 29) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 29)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  have h := decode_commitPrefixInstr ⟨idx - 0, by omega⟩
  have heq : 0 + (idx - 0) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid1Instr : Nat → Instruction
  | 2205 => .base (.ADD .x23 .x23 .x20)
  | 2206 => .base (.ADD .x18 .x18 .x21)
  | 2207 => .base (.BEQ .x10 .x19 (8#13))
  | 2208 => .base (.JAL .x0 (2088436#21))
  | 2209 => .base (.ADDI .x10 .x9 (4000#12))
  | 2210 => .base (.ADDI .x6 .x0 (128#12))
  | 2211 => .base (.SLLI .x6 .x6 (11#6))
  | 2212 => .base (.SLLI .x6 .x6 (11#6))
  | 2213 => .base (.ADD .x12 .x9 .x6)
  | 2214 => .base (.ADDI .x12 .x12 (4032#12))
  | 2215 => .base (.ADDI .x6 .x0 (127#12))
  | 2216 => .base (.SLLI .x6 .x6 (11#6))
  | 2217 => .base (.ADDI .x6 .x6 (2043#12))
  | 2218 => .base (.SLLI .x6 .x6 (11#6))
  | 2219 => .base (.ADDI .x6 .x6 (1952#12))
  | 2220 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1Instr (i : Fin 16) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨2205 + i.val, by omega⟩) =
      some (commitMid1Instr (2205 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1Instr (state : MachineState) (idx : Nat) (hlo : 2205 ≤ idx) (hhi : idx < 2221)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1Instr idx) := by
  have h := decode_commitMid1Instr ⟨idx - 2205, by omega⟩
  have heq : 2205 + (idx - 2205) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitMid2Instr : Nat → Instruction
  | 2605 => .base (.BNE .x10 .x19 (6656#13))
  | 2606 => .base (.ADDI .x6 .x0 (127#12))
  | 2607 => .base (.SLLI .x6 .x6 (11#6))
  | 2608 => .base (.ADDI .x6 .x6 (2047#12))
  | 2609 => .base (.SLLI .x6 .x6 (11#6))
  | 2610 => .base (.ADDI .x6 .x6 (1824#12))
  | 2611 => .base (.ADD .x19 .x9 .x6)
  | 2612 => .base (.ADDI .x10 .x10 (96#12))
  | 2613 => .base (.ADDI .x12 .x12 (64#12))
  | 2614 => .base .ECALL
  | 2615 => .base (.ADDI .x10 .x10 (96#12))
  | 2616 => .base (.ADDI .x12 .x12 (32#12))
  | 2617 => .base .ECALL
  | 2618 => .base (.BNE .x10 .x19 (8168#13))
  | 2619 => .base (.ADDI .x10 .x10 (96#12))
  | 2620 => .base (.ADDI .x12 .x12 (64#12))
  | 2621 => .base .ECALL
  | 2622 => .base (.LD .x6 .x10 (96#12))
  | 2623 => .base (.SD .x12 .x6 (32#12))
  | 2624 => .base (.LD .x6 .x10 (104#12))
  | 2625 => .base (.SD .x12 .x6 (40#12))
  | 2626 => .base (.LD .x6 .x10 (112#12))
  | 2627 => .base (.SD .x12 .x6 (48#12))
  | 2628 => .base (.LD .x6 .x10 (120#12))
  | 2629 => .base (.SD .x12 .x6 (56#12))
  | 2630 => .base (.ADDI .x24 .x2 (0#12))
  | 2631 => .base (.ADDI .x25 .x2 (704#12))
  | 2632 => .base (.LD .x6 .x24 (0#12))
  | 2633 => .base (.ADD .x10 .x9 .x6)
  | 2634 => .base (.ADDI .x10 .x10 (4000#12))
  | 2635 => .base (.LD .x6 .x24 (8#12))
  | 2636 => .base (.ADD .x12 .x9 .x6)
  | 2637 => .base (.ADDI .x12 .x12 (4032#12))
  | 2638 => .base (.LD .x20 .x24 (16#12))
  | 2639 => .base (.LD .x21 .x24 (24#12))
  | 2640 => .base (.SRLI .x22 .x20 (7#6))
  | 2641 => .base (.BEQ .x22 .x0 (2072#13))
  | 2642 => .base (.SLLI .x6 .x22 (12#6))
  | 2643 => .base (.SLLI .x7 .x22 (13#6))
  | 2644 => .base (.ADD .x6 .x6 .x7)
  | 2645 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid2Instr (i : Fin 41) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨2605 + i.val, by omega⟩) =
      some (commitMid2Instr (2605 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2Instr (state : MachineState) (idx : Nat) (hlo : 2605 ≤ idx) (hhi : idx < 2646)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2Instr idx) := by
  have h := decode_commitMid2Instr ⟨idx - 2605, by omega⟩
  have heq : 2605 + (idx - 2605) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def commitTailInstr : Nat → Instruction
  | 3158 => .base (.BNE .x10 .x19 (6144#13))
  | 3159 => .base (.ANDI .x22 .x20 (127#12))
  | 3160 => .base (.SRLI .x22 .x22 (1#6))
  | 3161 => .base (.BEQ .x22 .x0 (44#13))
  | 3162 => .base (.ADDI .x10 .x10 (96#12))
  | 3163 => .base (.ADDI .x12 .x12 (64#12))
  | 3164 => .base .ECALL
  | 3165 => .base (.SH .x12 .x0 (30#12))
  | 3166 => .base (.ADDI .x10 .x10 (96#12))
  | 3167 => .base (.ADDI .x12 .x12 (32#12))
  | 3168 => .base .ECALL
  | 3169 => .base (.SH .x12 .x0 (30#12))
  | 3170 => .base (.ADDI .x22 .x22 (4095#12))
  | 3171 => .base (.BNE .x22 .x0 (8156#13))
  | 3172 => .base (.ANDI .x22 .x20 (1#12))
  | 3173 => .base (.BEQ .x22 .x0 (60#13))
  | 3174 => .base (.ADDI .x10 .x10 (96#12))
  | 3175 => .base (.ADDI .x12 .x12 (64#12))
  | 3176 => .base .ECALL
  | 3177 => .base (.SH .x12 .x0 (30#12))
  | 3178 => .base (.BEQ .x21 .x0 (76#13))
  | 3179 => .base (.LD .x6 .x10 (96#12))
  | 3180 => .base (.SD .x12 .x6 (32#12))
  | 3181 => .base (.LD .x6 .x10 (104#12))
  | 3182 => .base (.SD .x12 .x6 (40#12))
  | 3183 => .base (.LD .x6 .x10 (112#12))
  | 3184 => .base (.SD .x12 .x6 (48#12))
  | 3185 => .base (.LD .x6 .x10 (120#12))
  | 3186 => .base (.SD .x12 .x6 (56#12))
  | 3187 => .base (.JAL .x0 (40#21))
  | 3188 => .base (.BEQ .x21 .x0 (36#13))
  | 3189 => .base (.LD .x6 .x10 (96#12))
  | 3190 => .base (.SD .x12 .x6 (64#12))
  | 3191 => .base (.LD .x6 .x10 (104#12))
  | 3192 => .base (.SD .x12 .x6 (72#12))
  | 3193 => .base (.LD .x6 .x10 (112#12))
  | 3194 => .base (.SD .x12 .x6 (80#12))
  | 3195 => .base (.LD .x6 .x10 (120#12))
  | 3196 => .base (.SD .x12 .x6 (88#12))
  | 3197 => .base (.ADDI .x24 .x24 (32#12))
  | 3198 => .base (.BNE .x24 .x25 (5928#13))
  | 3199 => .base (.ADDI .x6 .x0 (256#12))
  | 3200 => .base (.SLLI .x6 .x6 (11#6))
  | 3201 => .base (.SLLI .x6 .x6 (11#6))
  | 3202 => .base (.ADDI .x6 .x6 (928#12))
  | 3203 => .base (.ADD .x10 .x9 .x6)
  | 3204 => .base (.ADDI .x6 .x0 (256#12))
  | 3205 => .base (.SLLI .x6 .x6 (11#6))
  | 3206 => .base (.SLLI .x6 .x6 (11#6))
  | 3207 => .base (.ADDI .x6 .x6 (1024#12))
  | 3208 => .base (.ADD .x12 .x9 .x6)
  | 3209 => .base .ECALL
  | 3210 => .base (.LD .x6 .x12 (0#12))
  | 3211 => .base (.SD .x26 .x6 (0#12))
  | 3212 => .base (.LD .x6 .x12 (8#12))
  | 3213 => .base (.SD .x26 .x6 (8#12))
  | 3214 => .base (.LD .x6 .x12 (16#12))
  | 3215 => .base (.SD .x26 .x6 (16#12))
  | 3216 => .base (.LD .x6 .x12 (24#12))
  | 3217 => .base (.SD .x26 .x6 (24#12))
  | 3218 => .base (.ADDI .x5 .x0 (1#12))
  | 3219 => .base (.ADDI .x10 .x0 (0#12))
  | 3220 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr (i : Fin 63) :
    decodeInstruction (MoonArtifact.commitCode.get 32 ⟨3158 + i.val, by omega⟩) =
      some (commitTailInstr (3158 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 3158 ≤ idx) (hhi : idx < 3221)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  have h := decode_commitTailInstr ⟨idx - 3158, by omega⟩
  have heq : 3158 + (idx - 3158) = idx := by omega
  simp only [heq] at h
  exact fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _ h

def openingInstr : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (476#13))
  | 6 => .base (.ADDI .x6 .x0 (256#12))
  | 7 => .base (.SLLI .x6 .x6 (11#6))
  | 8 => .base (.SLLI .x6 .x6 (11#6))
  | 9 => .base (.ADDI .x6 .x6 (1056#12))
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
  | 20 => .base (.SLLI .x7 .x8 (4#6))
  | 21 => .base (.ADD .x10 .x18 .x7)
  | 22 => .base (.JAL .x1 (424#21))
  | 23 => .base (.ADDI .x25 .x25 (16#12))
  | 24 => .base (.DIVU .x22 .x8 .x19)
  | 25 => .base (.REMU .x23 .x8 .x19)
  | 26 => .base (.BEQ .x22 .x20 (112#13))
  | 27 => .base (.SLLI .x6 .x22 (6#6))
  | 28 => .base (.SLLI .x7 .x22 (5#6))
  | 29 => .base (.ADD .x28 .x6 .x7)
  | 30 => .base (.ADD .x28 .x9 .x28)
  | 31 => .base (.BEQ .x23 .x0 (40#13))
  | 32 => .base (.ADDI .x7 .x0 (1#12))
  | 33 => .base (.BEQ .x23 .x7 (60#13))
  | 34 => .base (.ADDI .x10 .x28 (0#12))
  | 35 => .base (.JAL .x1 (564#21))
  | 36 => .base (.ADDI .x25 .x25 (32#12))
  | 37 => .base (.ADDI .x10 .x28 (32#12))
  | 38 => .base (.JAL .x1 (552#21))
  | 39 => .base (.ADDI .x25 .x25 (32#12))
  | 40 => .base (.JAL .x0 (56#21))
  | 41 => .base (.ADDI .x10 .x28 (32#12))
  | 42 => .base (.JAL .x1 (536#21))
  | 43 => .base (.ADDI .x25 .x25 (32#12))
  | 44 => .base (.ADDI .x10 .x28 (64#12))
  | 45 => .base (.JAL .x1 (524#21))
  | 46 => .base (.ADDI .x25 .x25 (32#12))
  | 47 => .base (.JAL .x0 (28#21))
  | 48 => .base (.ADDI .x10 .x28 (0#12))
  | 49 => .base (.JAL .x1 (508#21))
  | 50 => .base (.ADDI .x25 .x25 (32#12))
  | 51 => .base (.ADDI .x10 .x28 (64#12))
  | 52 => .base (.JAL .x1 (496#21))
  | 53 => .base (.ADDI .x25 .x25 (32#12))
  | 54 => .base (.XORI .x28 .x22 (1#12))
  | 55 => .base (.SRLI .x6 .x28 (1#6))
  | 56 => .base (.ADD .x28 .x28 .x6)
  | 57 => .base (.SLLI .x28 .x28 (5#6))
  | 58 => .base (.LD .x6 .x2 (32#12))
  | 59 => .base (.ADD .x10 .x9 .x6)
  | 60 => .base (.ADD .x10 .x10 .x28)
  | 61 => .base (.JAL .x1 (460#21))
  | 62 => .base (.ADDI .x25 .x25 (32#12))
  | 63 => .base (.ADDI .x29 .x2 (64#12))
  | 64 => .base (.ADDI .x30 .x2 (480#12))
  | 65 => .base (.SRLI .x22 .x22 (1#6))
  | 66 => .base (.XORI .x28 .x22 (1#12))
  | 67 => .base (.LD .x7 .x29 (8#12))
  | 68 => .base (.BGEU .x28 .x7 (36#13))
  | 69 => .base (.SRLI .x6 .x28 (1#6))
  | 70 => .base (.ADD .x28 .x28 .x6)
  | 71 => .base (.SLLI .x28 .x28 (5#6))
  | 72 => .base (.LD .x6 .x29 (0#12))
  | 73 => .base (.ADD .x10 .x9 .x6)
  | 74 => .base (.ADD .x10 .x10 .x28)
  | 75 => .base (.JAL .x1 (280#21))
  | 76 => .base (.ADDI .x25 .x25 (30#12))
  | 77 => .base (.ADDI .x29 .x29 (32#12))
  | 78 => .base (.BNE .x29 .x30 (8140#13))
  | 79 => .base (.SRLI .x22 .x22 (1#6))
  | 80 => .base (.ADD .x6 .x21 .x22)
  | 81 => .base (.ADDI .x7 .x0 (1#12))
  | 82 => .base (.SB .x6 .x7 (0#12))
  | 83 => .base (.ADDI .x24 .x24 (8#12))
  | 84 => .base (.ADDI .x27 .x27 (4095#12))
  | 85 => .base (.BNE .x27 .x0 (7928#13))
  | 86 => .base (.ADDI .x29 .x2 (480#12))
  | 87 => .base (.ADDI .x30 .x2 (768#12))
  | 88 => .base (.LD .x18 .x29 (0#12))
  | 89 => .base (.ADD .x18 .x9 .x18)
  | 90 => .base (.LD .x19 .x29 (8#12))
  | 91 => .base (.LD .x20 .x29 (16#12))
  | 92 => .base (.ADD .x20 .x21 .x20)
  | 93 => .base (.LD .x22 .x29 (48#12))
  | 94 => .base (.ADD .x22 .x21 .x22)
  | 95 => .base (.SRLI .x23 .x19 (1#6))
  | 96 => .base (.ADDI .x24 .x0 (0#12))
  | 97 => .base (.SLLI .x6 .x24 (1#6))
  | 98 => .base (.ADD .x6 .x20 .x6)
  | 99 => .base (.LBU .x7 .x6 (0#12))
  | 100 => .base (.LBU .x8 .x6 (1#12))
  | 101 => .base (.OR .x11 .x7 .x8)
  | 102 => .base (.ADD .x6 .x22 .x24)
  | 103 => .base (.SB .x6 .x11 (0#12))
  | 104 => .base (.BEQ .x7 .x8 (36#13))
  | 105 => .base (.SLLI .x6 .x24 (6#6))
  | 106 => .base (.SLLI .x11 .x24 (5#6))
  | 107 => .base (.ADD .x10 .x6 .x11)
  | 108 => .base (.ADD .x10 .x18 .x10)
  | 109 => .base (.BEQ .x7 .x0 (8#13))
  | 110 => .base (.ADDI .x10 .x10 (32#12))
  | 111 => .base (.JAL .x1 (136#21))
  | 112 => .base (.ADDI .x25 .x25 (30#12))
  | 113 => .base (.ADDI .x24 .x24 (1#12))
  | 114 => .base (.BNE .x24 .x23 (8124#13))
  | 115 => .base (.ANDI .x6 .x19 (1#12))
  | 116 => .base (.BEQ .x6 .x0 (24#13))
  | 117 => .base (.SLLI .x7 .x23 (1#6))
  | 118 => .base (.ADD .x7 .x20 .x7)
  | 119 => .base (.LBU .x8 .x7 (0#12))
  | 120 => .base (.ADD .x7 .x22 .x23)
  | 121 => .base (.SB .x7 .x8 (0#12))
  | 122 => .base (.ADDI .x29 .x29 (32#12))
  | 123 => .base (.BNE .x29 .x30 (8052#13))
  | 124 => .base (.SUB .x11 .x25 .x26)
  | 125 => .base (.ADDI .x5 .x0 (1#12))
  | 126 => .base (.ADDI .x10 .x0 (0#12))
  | 127 => .base .ECALL
  | 128 => .base (.LHU .x6 .x10 (0#12))
  | 129 => .base (.SH .x25 .x6 (0#12))
  | 130 => .base (.LHU .x6 .x10 (2#12))
  | 131 => .base (.SH .x25 .x6 (2#12))
  | 132 => .base (.LHU .x6 .x10 (4#12))
  | 133 => .base (.SH .x25 .x6 (4#12))
  | 134 => .base (.LHU .x6 .x10 (6#12))
  | 135 => .base (.SH .x25 .x6 (6#12))
  | 136 => .base (.LHU .x6 .x10 (8#12))
  | 137 => .base (.SH .x25 .x6 (8#12))
  | 138 => .base (.LHU .x6 .x10 (10#12))
  | 139 => .base (.SH .x25 .x6 (10#12))
  | 140 => .base (.LHU .x6 .x10 (12#12))
  | 141 => .base (.SH .x25 .x6 (12#12))
  | 142 => .base (.LHU .x6 .x10 (14#12))
  | 143 => .base (.SH .x25 .x6 (14#12))
  | 144 => .base (.JALR .x0 .x1 (0#12))
  | 145 => .base (.LHU .x6 .x10 (0#12))
  | 146 => .base (.SH .x25 .x6 (0#12))
  | 147 => .base (.LHU .x6 .x10 (2#12))
  | 148 => .base (.SH .x25 .x6 (2#12))
  | 149 => .base (.LHU .x6 .x10 (4#12))
  | 150 => .base (.SH .x25 .x6 (4#12))
  | 151 => .base (.LHU .x6 .x10 (6#12))
  | 152 => .base (.SH .x25 .x6 (6#12))
  | 153 => .base (.LHU .x6 .x10 (8#12))
  | 154 => .base (.SH .x25 .x6 (8#12))
  | 155 => .base (.LHU .x6 .x10 (10#12))
  | 156 => .base (.SH .x25 .x6 (10#12))
  | 157 => .base (.LHU .x6 .x10 (12#12))
  | 158 => .base (.SH .x25 .x6 (12#12))
  | 159 => .base (.LHU .x6 .x10 (14#12))
  | 160 => .base (.SH .x25 .x6 (14#12))
  | 161 => .base (.LHU .x6 .x10 (16#12))
  | 162 => .base (.SH .x25 .x6 (16#12))
  | 163 => .base (.LHU .x6 .x10 (18#12))
  | 164 => .base (.SH .x25 .x6 (18#12))
  | 165 => .base (.LHU .x6 .x10 (20#12))
  | 166 => .base (.SH .x25 .x6 (20#12))
  | 167 => .base (.LHU .x6 .x10 (22#12))
  | 168 => .base (.SH .x25 .x6 (22#12))
  | 169 => .base (.LHU .x6 .x10 (24#12))
  | 170 => .base (.SH .x25 .x6 (24#12))
  | 171 => .base (.LHU .x6 .x10 (26#12))
  | 172 => .base (.SH .x25 .x6 (26#12))
  | 173 => .base (.LHU .x6 .x10 (28#12))
  | 174 => .base (.SH .x25 .x6 (28#12))
  | 175 => .base (.JALR .x0 .x1 (0#12))
  | 176 => .base (.LHU .x6 .x10 (0#12))
  | 177 => .base (.SH .x25 .x6 (0#12))
  | 178 => .base (.LHU .x6 .x10 (2#12))
  | 179 => .base (.SH .x25 .x6 (2#12))
  | 180 => .base (.LHU .x6 .x10 (4#12))
  | 181 => .base (.SH .x25 .x6 (4#12))
  | 182 => .base (.LHU .x6 .x10 (6#12))
  | 183 => .base (.SH .x25 .x6 (6#12))
  | 184 => .base (.LHU .x6 .x10 (8#12))
  | 185 => .base (.SH .x25 .x6 (8#12))
  | 186 => .base (.LHU .x6 .x10 (10#12))
  | 187 => .base (.SH .x25 .x6 (10#12))
  | 188 => .base (.LHU .x6 .x10 (12#12))
  | 189 => .base (.SH .x25 .x6 (12#12))
  | 190 => .base (.LHU .x6 .x10 (14#12))
  | 191 => .base (.SH .x25 .x6 (14#12))
  | 192 => .base (.LHU .x6 .x10 (16#12))
  | 193 => .base (.SH .x25 .x6 (16#12))
  | 194 => .base (.LHU .x6 .x10 (18#12))
  | 195 => .base (.SH .x25 .x6 (18#12))
  | 196 => .base (.LHU .x6 .x10 (20#12))
  | 197 => .base (.SH .x25 .x6 (20#12))
  | 198 => .base (.LHU .x6 .x10 (22#12))
  | 199 => .base (.SH .x25 .x6 (22#12))
  | 200 => .base (.LHU .x6 .x10 (24#12))
  | 201 => .base (.SH .x25 .x6 (24#12))
  | 202 => .base (.LHU .x6 .x10 (26#12))
  | 203 => .base (.SH .x25 .x6 (26#12))
  | 204 => .base (.LHU .x6 .x10 (28#12))
  | 205 => .base (.SH .x25 .x6 (28#12))
  | 206 => .base (.LHU .x6 .x10 (30#12))
  | 207 => .base (.SH .x25 .x6 (30#12))
  | 208 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

private theorem decode_opening_0 (i : Fin 128) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr i.val) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 81) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨128 + i.val, by omega⟩) =
      some (openingInstr (128 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 209)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .opening) state = some (openingInstr idx) := by
  apply fetch_of_packed MoonArtifact.openingCode _ state idx hhi hpc
  by_cases h0 : idx < 128
  · exact decode_opening_0 ⟨idx, h0⟩
  · have h := decode_opening_1 ⟨idx - 128, by omega⟩
    have heq : 128 + (idx - 128) = idx := by omega
    simpa only [heq] using h

def checkInstr : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (1316#13))
  | 8 => .base (.JAL .x0 (1300#21))
  | 9 => .base (.ADDI .x21 .x0 (256#12))
  | 10 => .base (.ADDI .x18 .x0 (2#12))
  | 11 => .base (.SLLI .x18 .x18 (11#6))
  | 12 => .base (.ADDI .x19 .x0 (4#12))
  | 13 => .base (.SLLI .x19 .x19 (11#6))
  | 14 => .base (.ADDI .x5 .x0 (0#12))
  | 15 => .base (.ADDI .x11 .x0 (96#12))
  | 16 => .base (.ADDI .x13 .x0 (0#12))
  | 17 => .base (.LD .x20 .x24 (0#12))
  | 18 => .base (.ADDI .x6 .x25 (16#12))
  | 19 => .base (.BLTU .x31 .x6 (1268#13))
  | 20 => .base (.ADDI .x12 .x21 (0#12))
  | 21 => .base (.JAL .x1 (1272#21))
  | 22 => .base (.ADDI .x25 .x25 (16#12))
  | 23 => .base (.SLLI .x6 .x20 (8#6))
  | 24 => .base (.ADDI .x7 .x0 (1#12))
  | 25 => .base (.SLLI .x7 .x7 (11#6))
  | 26 => .base (.ADDI .x7 .x7 (2024#12))
  | 27 => .base (.ADD .x6 .x6 .x7)
  | 28 => .base (.SD .x21 .x6 (16#12))
  | 29 => .base (.LD .x6 .x8 (0#12))
  | 30 => .base (.SD .x21 .x6 (24#12))
  | 31 => .base (.LD .x6 .x8 (8#12))
  | 32 => .base (.SD .x21 .x6 (32#12))
  | 33 => .base (.LD .x6 .x8 (16#12))
  | 34 => .base (.SD .x21 .x6 (40#12))
  | 35 => .base (.LD .x6 .x8 (24#12))
  | 36 => .base (.SD .x21 .x6 (48#12))
  | 37 => .base (.LD .x6 .x8 (32#12))
  | 38 => .base (.SD .x21 .x6 (56#12))
  | 39 => .base (.LD .x6 .x8 (40#12))
  | 40 => .base (.SD .x21 .x6 (64#12))
  | 41 => .base (.LD .x6 .x8 (48#12))
  | 42 => .base (.SD .x21 .x6 (72#12))
  | 43 => .base (.LD .x6 .x8 (56#12))
  | 44 => .base (.SD .x21 .x6 (80#12))
  | 45 => .base (.LD .x6 .x8 (64#12))
  | 46 => .base (.SD .x21 .x6 (88#12))
  | 47 => .base (.ADDI .x10 .x21 (0#12))
  | 48 => .base (.ADDI .x12 .x21 (0#12))
  | 49 => .base .ECALL
  | 50 => .base (.LD .x6 .x8 (72#12))
  | 51 => .base (.SD .x21 .x6 (32#12))
  | 52 => .base (.LD .x6 .x8 (80#12))
  | 53 => .base (.SD .x21 .x6 (40#12))
  | 54 => .base (.LD .x6 .x8 (88#12))
  | 55 => .base (.SD .x21 .x6 (48#12))
  | 56 => .base (.LD .x6 .x8 (96#12))
  | 57 => .base (.SD .x21 .x6 (56#12))
  | 58 => .base (.LD .x6 .x8 (104#12))
  | 59 => .base (.SD .x21 .x6 (64#12))
  | 60 => .base (.LD .x6 .x8 (112#12))
  | 61 => .base (.SD .x21 .x6 (72#12))
  | 62 => .base (.LD .x6 .x8 (120#12))
  | 63 => .base (.SD .x21 .x6 (80#12))
  | 64 => .base (.LD .x6 .x8 (128#12))
  | 65 => .base (.SD .x21 .x6 (88#12))
  | 66 => .base .ECALL
  | 67 => .base (.LD .x6 .x8 (136#12))
  | 68 => .base (.SD .x21 .x6 (32#12))
  | 69 => .base (.LD .x6 .x8 (144#12))
  | 70 => .base (.SD .x21 .x6 (40#12))
  | 71 => .base (.LD .x6 .x8 (152#12))
  | 72 => .base (.SD .x21 .x6 (48#12))
  | 73 => .base (.LD .x6 .x8 (160#12))
  | 74 => .base (.SD .x21 .x6 (56#12))
  | 75 => .base (.LD .x6 .x8 (168#12))
  | 76 => .base (.SD .x21 .x6 (64#12))
  | 77 => .base (.LD .x6 .x8 (176#12))
  | 78 => .base (.SD .x21 .x6 (72#12))
  | 79 => .base (.LD .x6 .x8 (184#12))
  | 80 => .base (.SD .x21 .x6 (80#12))
  | 81 => .base (.LD .x6 .x8 (192#12))
  | 82 => .base (.SD .x21 .x6 (88#12))
  | 83 => .base .ECALL
  | 84 => .base (.LD .x6 .x8 (192#12))
  | 85 => .base (.SD .x21 .x6 (32#12))
  | 86 => .base (.LD .x6 .x8 (200#12))
  | 87 => .base (.SD .x21 .x6 (40#12))
  | 88 => .base (.LD .x6 .x8 (208#12))
  | 89 => .base (.SD .x21 .x6 (48#12))
  | 90 => .base (.LD .x6 .x8 (216#12))
  | 91 => .base (.SD .x21 .x6 (56#12))
  | 92 => .base (.LD .x6 .x8 (224#12))
  | 93 => .base (.SD .x21 .x6 (64#12))
  | 94 => .base (.LD .x6 .x8 (232#12))
  | 95 => .base (.SD .x21 .x6 (72#12))
  | 96 => .base (.LD .x6 .x8 (240#12))
  | 97 => .base (.SD .x21 .x6 (80#12))
  | 98 => .base (.LD .x6 .x8 (248#12))
  | 99 => .base (.SD .x21 .x6 (88#12))
  | 100 => .base .ECALL
  | 101 => .base (.ADDI .x7 .x0 (3#12))
  | 102 => .base (.DIVU .x22 .x20 .x7)
  | 103 => .base (.REMU .x23 .x20 .x7)
  | 104 => .base (.ADDI .x6 .x0 (1#12))
  | 105 => .base (.SLLI .x6 .x6 (11#6))
  | 106 => .base (.ADDI .x6 .x6 (682#12))
  | 107 => .base (.SLLI .x6 .x6 (11#6))
  | 108 => .base (.ADDI .x6 .x6 (1365#12))
  | 109 => .base (.BEQ .x22 .x6 (180#13))
  | 110 => .base (.ADDI .x6 .x25 (64#12))
  | 111 => .base (.BLTU .x31 .x6 (900#13))
  | 112 => .base (.BEQ .x23 .x0 (72#13))
  | 113 => .base (.ADDI .x7 .x0 (1#12))
  | 114 => .base (.BEQ .x23 .x7 (92#13))
  | 115 => .base (.LD .x6 .x21 (0#12))
  | 116 => .base (.SD .x21 .x6 (64#12))
  | 117 => .base (.LD .x6 .x21 (8#12))
  | 118 => .base (.SD .x21 .x6 (72#12))
  | 119 => .base (.LD .x6 .x21 (16#12))
  | 120 => .base (.SD .x21 .x6 (80#12))
  | 121 => .base (.LD .x6 .x21 (24#12))
  | 122 => .base (.SD .x21 .x6 (88#12))
  | 123 => .base (.ADDI .x12 .x21 (0#12))
  | 124 => .base (.JAL .x1 (1052#21))
  | 125 => .base (.ADDI .x25 .x25 (32#12))
  | 126 => .base (.ADDI .x12 .x21 (32#12))
  | 127 => .base (.JAL .x1 (1040#21))
  | 128 => .base (.ADDI .x25 .x25 (32#12))
  | 129 => .base (.JAL .x0 (88#21))
  | 130 => .base (.ADDI .x12 .x21 (32#12))
  | 131 => .base (.JAL .x1 (1024#21))
  | 132 => .base (.ADDI .x25 .x25 (32#12))
  | 133 => .base (.ADDI .x12 .x21 (64#12))
  | 134 => .base (.JAL .x1 (1012#21))
  | 135 => .base (.ADDI .x25 .x25 (32#12))
  | 136 => .base (.JAL .x0 (60#21))
  | 137 => .base (.LD .x6 .x21 (0#12))
  | 138 => .base (.SD .x21 .x6 (32#12))
  | 139 => .base (.LD .x6 .x21 (8#12))
  | 140 => .base (.SD .x21 .x6 (40#12))
  | 141 => .base (.LD .x6 .x21 (16#12))
  | 142 => .base (.SD .x21 .x6 (48#12))
  | 143 => .base (.LD .x6 .x21 (24#12))
  | 144 => .base (.SD .x21 .x6 (56#12))
  | 145 => .base (.ADDI .x12 .x21 (0#12))
  | 146 => .base (.JAL .x1 (964#21))
  | 147 => .base (.ADDI .x25 .x25 (32#12))
  | 148 => .base (.ADDI .x12 .x21 (64#12))
  | 149 => .base (.JAL .x1 (952#21))
  | 150 => .base (.ADDI .x25 .x25 (32#12))
  | 151 => .base (.ADDI .x10 .x21 (0#12))
  | 152 => .base (.ADDI .x12 .x21 (0#12))
  | 153 => .base .ECALL
  | 154 => .base (.ADDI .x6 .x25 (32#12))
  | 155 => .base (.BLTU .x31 .x6 (724#13))
  | 156 => .base (.SD .x21 .x0 (64#12))
  | 157 => .base (.SD .x21 .x0 (72#12))
  | 158 => .base (.SD .x21 .x0 (80#12))
  | 159 => .base (.SD .x21 .x0 (88#12))
  | 160 => .base (.ANDI .x7 .x22 (1#12))
  | 161 => .base (.BEQ .x7 .x0 (52#13))
  | 162 => .base (.LD .x6 .x21 (0#12))
  | 163 => .base (.SD .x21 .x6 (32#12))
  | 164 => .base (.LD .x6 .x21 (8#12))
  | 165 => .base (.SD .x21 .x6 (40#12))
  | 166 => .base (.LD .x6 .x21 (16#12))
  | 167 => .base (.SD .x21 .x6 (48#12))
  | 168 => .base (.LD .x6 .x21 (24#12))
  | 169 => .base (.SD .x21 .x6 (56#12))
  | 170 => .base (.ADDI .x12 .x21 (0#12))
  | 171 => .base (.JAL .x1 (864#21))
  | 172 => .base (.ADDI .x25 .x25 (32#12))
  | 173 => .base (.JAL .x0 (16#21))
  | 174 => .base (.ADDI .x12 .x21 (32#12))
  | 175 => .base (.JAL .x1 (848#21))
  | 176 => .base (.ADDI .x25 .x25 (32#12))
  | 177 => .base (.ADDI .x10 .x21 (0#12))
  | 178 => .base (.ADDI .x12 .x21 (0#12))
  | 179 => .base .ECALL
  | 180 => .base (.SH .x21 .x0 (30#12))
  | 181 => .base (.ADDI .x29 .x2 (64#12))
  | 182 => .base (.ADDI .x30 .x2 (480#12))
  | 183 => .base (.SRLI .x22 .x22 (1#6))
  | 184 => .base (.XORI .x28 .x22 (1#12))
  | 185 => .base (.LD .x7 .x29 (8#12))
  | 186 => .base (.BGEU .x28 .x7 (104#13))
  | 187 => .base (.ADDI .x6 .x25 (30#12))
  | 188 => .base (.BLTU .x31 .x6 (592#13))
  | 189 => .base (.ANDI .x7 .x22 (1#12))
  | 190 => .base (.BEQ .x7 .x0 (56#13))
  | 191 => .base (.LD .x6 .x21 (0#12))
  | 192 => .base (.SD .x21 .x6 (32#12))
  | 193 => .base (.LD .x6 .x21 (8#12))
  | 194 => .base (.SD .x21 .x6 (40#12))
  | 195 => .base (.LD .x6 .x21 (16#12))
  | 196 => .base (.SD .x21 .x6 (48#12))
  | 197 => .base (.LD .x6 .x21 (24#12))
  | 198 => .base (.SD .x21 .x6 (56#12))
  | 199 => .base (.ADDI .x12 .x21 (0#12))
  | 200 => .base (.JAL .x1 (624#21))
  | 201 => .base (.SH .x21 .x0 (30#12))
  | 202 => .base (.ADDI .x25 .x25 (30#12))
  | 203 => .base (.JAL .x0 (20#21))
  | 204 => .base (.ADDI .x12 .x21 (32#12))
  | 205 => .base (.JAL .x1 (604#21))
  | 206 => .base (.SH .x21 .x0 (62#12))
  | 207 => .base (.ADDI .x25 .x25 (30#12))
  | 208 => .base (.ADDI .x10 .x21 (0#12))
  | 209 => .base (.ADDI .x12 .x21 (0#12))
  | 210 => .base .ECALL
  | 211 => .base (.SH .x21 .x0 (30#12))
  | 212 => .base (.ADDI .x29 .x29 (32#12))
  | 213 => .base (.BNE .x29 .x30 (8072#13))
  | 214 => .base (.SRLI .x22 .x22 (1#6))
  | 215 => .base (.SRLI .x6 .x22 (1#6))
  | 216 => .base (.ADD .x6 .x22 .x6)
  | 217 => .base (.SLLI .x6 .x6 (5#6))
  | 218 => .base (.ADD .x28 .x19 .x6)
  | 219 => .base (.ADD .x29 .x18 .x22)
  | 220 => .base (.LBU .x7 .x29 (0#12))
  | 221 => .base (.BNE .x7 .x0 (48#13))
  | 222 => .base (.ADDI .x7 .x0 (1#12))
  | 223 => .base (.SB .x29 .x7 (0#12))
  | 224 => .base (.LD .x6 .x21 (0#12))
  | 225 => .base (.SD .x28 .x6 (0#12))
  | 226 => .base (.LD .x6 .x21 (8#12))
  | 227 => .base (.SD .x28 .x6 (8#12))
  | 228 => .base (.LD .x6 .x21 (16#12))
  | 229 => .base (.SD .x28 .x6 (16#12))
  | 230 => .base (.LD .x6 .x21 (24#12))
  | 231 => .base (.SD .x28 .x6 (24#12))
  | 232 => .base (.JAL .x0 (52#21))
  | 233 => .base (.LD .x6 .x21 (0#12))
  | 234 => .base (.LD .x7 .x28 (0#12))
  | 235 => .base (.BNE .x6 .x7 (404#13))
  | 236 => .base (.LD .x6 .x21 (8#12))
  | 237 => .base (.LD .x7 .x28 (8#12))
  | 238 => .base (.BNE .x6 .x7 (392#13))
  | 239 => .base (.LD .x6 .x21 (16#12))
  | 240 => .base (.LD .x7 .x28 (16#12))
  | 241 => .base (.BNE .x6 .x7 (380#13))
  | 242 => .base (.LD .x6 .x21 (24#12))
  | 243 => .base (.LD .x7 .x28 (24#12))
  | 244 => .base (.BNE .x6 .x7 (368#13))
  | 245 => .base (.ADDI .x24 .x24 (8#12))
  | 246 => .base (.ADDI .x8 .x8 (256#12))
  | 247 => .base (.ADDI .x27 .x27 (4095#12))
  | 248 => .base (.BNE .x27 .x0 (7268#13))
  | 249 => .base (.ADDI .x29 .x2 (480#12))
  | 250 => .base (.ADDI .x30 .x2 (768#12))
  | 251 => .base (.LD .x20 .x29 (8#12))
  | 252 => .base (.LD .x14 .x29 (16#12))
  | 253 => .base (.ADD .x14 .x18 .x14)
  | 254 => .base (.LD .x15 .x29 (48#12))
  | 255 => .base (.ADD .x15 .x18 .x15)
  | 256 => .base (.LD .x16 .x29 (24#12))
  | 257 => .base (.ADD .x16 .x19 .x16)
  | 258 => .base (.LD .x17 .x29 (56#12))
  | 259 => .base (.ADD .x17 .x19 .x17)
  | 260 => .base (.SRLI .x22 .x20 (1#6))
  | 261 => .base (.ADDI .x23 .x0 (0#12))
  | 262 => .base (.SLLI .x6 .x23 (1#6))
  | 263 => .base (.ADD .x6 .x14 .x6)
  | 264 => .base (.LBU .x7 .x6 (0#12))
  | 265 => .base (.LBU .x8 .x6 (1#12))
  | 266 => .base (.OR .x28 .x7 .x8)
  | 267 => .base (.BEQ .x28 .x0 (92#13))
  | 268 => .base (.ADD .x6 .x15 .x23)
  | 269 => .base (.SB .x6 .x28 (0#12))
  | 270 => .base (.SLLI .x6 .x23 (6#6))
  | 271 => .base (.SLLI .x28 .x23 (5#6))
  | 272 => .base (.ADD .x10 .x6 .x28)
  | 273 => .base (.ADD .x10 .x16 .x10)
  | 274 => .base (.BEQ .x7 .x8 (32#13))
  | 275 => .base (.ADDI .x6 .x25 (30#12))
  | 276 => .base (.BLTU .x31 .x6 (240#13))
  | 277 => .base (.ADDI .x12 .x10 (0#12))
  | 278 => .base (.BEQ .x7 .x0 (8#13))
  | 279 => .base (.ADDI .x12 .x10 (32#12))
  | 280 => .base (.JAL .x1 (304#21))
  | 281 => .base (.ADDI .x25 .x25 (30#12))
  | 282 => .base (.SRLI .x6 .x23 (1#6))
  | 283 => .base (.ADD .x6 .x23 .x6)
  | 284 => .base (.SLLI .x6 .x6 (5#6))
  | 285 => .base (.ADD .x12 .x17 .x6)
  | 286 => .base .ECALL
  | 287 => .base (.ADDI .x6 .x2 (736#12))
  | 288 => .base (.BEQ .x29 .x6 (8#13))
  | 289 => .base (.SH .x12 .x0 (30#12))
  | 290 => .base (.ADDI .x23 .x23 (1#12))
  | 291 => .base (.BNE .x23 .x22 (8076#13))
  | 292 => .base (.ANDI .x6 .x20 (1#12))
  | 293 => .base (.BEQ .x6 .x0 (92#13))
  | 294 => .base (.SLLI .x7 .x22 (1#6))
  | 295 => .base (.ADD .x7 .x14 .x7)
  | 296 => .base (.LBU .x8 .x7 (0#12))
  | 297 => .base (.BEQ .x8 .x0 (76#13))
  | 298 => .base (.ADD .x7 .x15 .x22)
  | 299 => .base (.SB .x7 .x8 (0#12))
  | 300 => .base (.SLLI .x6 .x22 (6#6))
  | 301 => .base (.SLLI .x7 .x22 (5#6))
  | 302 => .base (.ADD .x10 .x6 .x7)
  | 303 => .base (.ADD .x10 .x16 .x10)
  | 304 => .base (.SRLI .x6 .x22 (1#6))
  | 305 => .base (.ADD .x6 .x22 .x6)
  | 306 => .base (.SLLI .x6 .x6 (5#6))
  | 307 => .base (.ADD .x12 .x17 .x6)
  | 308 => .base (.LD .x6 .x10 (0#12))
  | 309 => .base (.SD .x12 .x6 (0#12))
  | 310 => .base (.LD .x6 .x10 (8#12))
  | 311 => .base (.SD .x12 .x6 (8#12))
  | 312 => .base (.LD .x6 .x10 (16#12))
  | 313 => .base (.SD .x12 .x6 (16#12))
  | 314 => .base (.LD .x6 .x10 (24#12))
  | 315 => .base (.SD .x12 .x6 (24#12))
  | 316 => .base (.ADDI .x29 .x29 (32#12))
  | 317 => .base (.BNE .x29 .x30 (7928#13))
  | 318 => .base (.BNE .x25 .x31 (72#13))
  | 319 => .base (.LD .x6 .x2 (792#12))
  | 320 => .base (.ADD .x10 .x19 .x6)
  | 321 => .base (.LD .x6 .x10 (0#12))
  | 322 => .base (.LD .x7 .x26 (0#12))
  | 323 => .base (.BNE .x6 .x7 (52#13))
  | 324 => .base (.LD .x6 .x10 (8#12))
  | 325 => .base (.LD .x7 .x26 (8#12))
  | 326 => .base (.BNE .x6 .x7 (40#13))
  | 327 => .base (.LD .x6 .x10 (16#12))
  | 328 => .base (.LD .x7 .x26 (16#12))
  | 329 => .base (.BNE .x6 .x7 (28#13))
  | 330 => .base (.LD .x6 .x10 (24#12))
  | 331 => .base (.LD .x7 .x26 (24#12))
  | 332 => .base (.BNE .x6 .x7 (16#13))
  | 333 => .base (.ADDI .x5 .x0 (1#12))
  | 334 => .base (.ADDI .x10 .x0 (0#12))
  | 335 => .base .ECALL
  | 336 => .base (.ADDI .x5 .x0 (1#12))
  | 337 => .base (.ADDI .x10 .x0 (1#12))
  | 338 => .base .ECALL
  | 339 => .base (.LHU .x6 .x25 (0#12))
  | 340 => .base (.SH .x12 .x6 (0#12))
  | 341 => .base (.LHU .x6 .x25 (2#12))
  | 342 => .base (.SH .x12 .x6 (2#12))
  | 343 => .base (.LHU .x6 .x25 (4#12))
  | 344 => .base (.SH .x12 .x6 (4#12))
  | 345 => .base (.LHU .x6 .x25 (6#12))
  | 346 => .base (.SH .x12 .x6 (6#12))
  | 347 => .base (.LHU .x6 .x25 (8#12))
  | 348 => .base (.SH .x12 .x6 (8#12))
  | 349 => .base (.LHU .x6 .x25 (10#12))
  | 350 => .base (.SH .x12 .x6 (10#12))
  | 351 => .base (.LHU .x6 .x25 (12#12))
  | 352 => .base (.SH .x12 .x6 (12#12))
  | 353 => .base (.LHU .x6 .x25 (14#12))
  | 354 => .base (.SH .x12 .x6 (14#12))
  | 355 => .base (.JALR .x0 .x1 (0#12))
  | 356 => .base (.LHU .x6 .x25 (0#12))
  | 357 => .base (.SH .x12 .x6 (0#12))
  | 358 => .base (.LHU .x6 .x25 (2#12))
  | 359 => .base (.SH .x12 .x6 (2#12))
  | 360 => .base (.LHU .x6 .x25 (4#12))
  | 361 => .base (.SH .x12 .x6 (4#12))
  | 362 => .base (.LHU .x6 .x25 (6#12))
  | 363 => .base (.SH .x12 .x6 (6#12))
  | 364 => .base (.LHU .x6 .x25 (8#12))
  | 365 => .base (.SH .x12 .x6 (8#12))
  | 366 => .base (.LHU .x6 .x25 (10#12))
  | 367 => .base (.SH .x12 .x6 (10#12))
  | 368 => .base (.LHU .x6 .x25 (12#12))
  | 369 => .base (.SH .x12 .x6 (12#12))
  | 370 => .base (.LHU .x6 .x25 (14#12))
  | 371 => .base (.SH .x12 .x6 (14#12))
  | 372 => .base (.LHU .x6 .x25 (16#12))
  | 373 => .base (.SH .x12 .x6 (16#12))
  | 374 => .base (.LHU .x6 .x25 (18#12))
  | 375 => .base (.SH .x12 .x6 (18#12))
  | 376 => .base (.LHU .x6 .x25 (20#12))
  | 377 => .base (.SH .x12 .x6 (20#12))
  | 378 => .base (.LHU .x6 .x25 (22#12))
  | 379 => .base (.SH .x12 .x6 (22#12))
  | 380 => .base (.LHU .x6 .x25 (24#12))
  | 381 => .base (.SH .x12 .x6 (24#12))
  | 382 => .base (.LHU .x6 .x25 (26#12))
  | 383 => .base (.SH .x12 .x6 (26#12))
  | 384 => .base (.LHU .x6 .x25 (28#12))
  | 385 => .base (.SH .x12 .x6 (28#12))
  | 386 => .base (.JALR .x0 .x1 (0#12))
  | 387 => .base (.LHU .x6 .x25 (0#12))
  | 388 => .base (.SH .x12 .x6 (0#12))
  | 389 => .base (.LHU .x6 .x25 (2#12))
  | 390 => .base (.SH .x12 .x6 (2#12))
  | 391 => .base (.LHU .x6 .x25 (4#12))
  | 392 => .base (.SH .x12 .x6 (4#12))
  | 393 => .base (.LHU .x6 .x25 (6#12))
  | 394 => .base (.SH .x12 .x6 (6#12))
  | 395 => .base (.LHU .x6 .x25 (8#12))
  | 396 => .base (.SH .x12 .x6 (8#12))
  | 397 => .base (.LHU .x6 .x25 (10#12))
  | 398 => .base (.SH .x12 .x6 (10#12))
  | 399 => .base (.LHU .x6 .x25 (12#12))
  | 400 => .base (.SH .x12 .x6 (12#12))
  | 401 => .base (.LHU .x6 .x25 (14#12))
  | 402 => .base (.SH .x12 .x6 (14#12))
  | 403 => .base (.LHU .x6 .x25 (16#12))
  | 404 => .base (.SH .x12 .x6 (16#12))
  | 405 => .base (.LHU .x6 .x25 (18#12))
  | 406 => .base (.SH .x12 .x6 (18#12))
  | 407 => .base (.LHU .x6 .x25 (20#12))
  | 408 => .base (.SH .x12 .x6 (20#12))
  | 409 => .base (.LHU .x6 .x25 (22#12))
  | 410 => .base (.SH .x12 .x6 (22#12))
  | 411 => .base (.LHU .x6 .x25 (24#12))
  | 412 => .base (.SH .x12 .x6 (24#12))
  | 413 => .base (.LHU .x6 .x25 (26#12))
  | 414 => .base (.SH .x12 .x6 (26#12))
  | 415 => .base (.LHU .x6 .x25 (28#12))
  | 416 => .base (.SH .x12 .x6 (28#12))
  | 417 => .base (.LHU .x6 .x25 (30#12))
  | 418 => .base (.SH .x12 .x6 (30#12))
  | 419 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

private theorem decode_check_0 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨0 + i.val, by omega⟩) =
      some (checkInstr (0 + i.val)) := by
  revert i; decide

private theorem decode_check_1 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨70 + i.val, by omega⟩) =
      some (checkInstr (70 + i.val)) := by
  revert i; decide

private theorem decode_check_2 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨140 + i.val, by omega⟩) =
      some (checkInstr (140 + i.val)) := by
  revert i; decide

private theorem decode_check_3 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨210 + i.val, by omega⟩) =
      some (checkInstr (210 + i.val)) := by
  revert i; decide

set_option maxRecDepth 2000 in
private theorem decode_check_4 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨280 + i.val, by omega⟩) =
      some (checkInstr (280 + i.val)) := by
  revert i; decide

set_option maxRecDepth 2000 in
private theorem decode_check_5 (i : Fin 70) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨350 + i.val, by omega⟩) =
      some (checkInstr (350 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 420)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .check) state = some (checkInstr idx) := by
  apply fetch_of_packed MoonArtifact.checkCode _ state idx hhi hpc
  by_cases h0 : idx < 70
  · simpa using decode_check_0 ⟨idx, h0⟩
  · by_cases h1 : idx < 140
    · have h := decode_check_1 ⟨idx - 70, by omega⟩
      simpa only [show 70 + (idx - 70) = idx by omega] using h
    · by_cases h2 : idx < 210
      · have h := decode_check_2 ⟨idx - 140, by omega⟩
        simpa only [show 140 + (idx - 140) = idx by omega] using h
      · by_cases h3 : idx < 280
        · have h := decode_check_3 ⟨idx - 210, by omega⟩
          simpa only [show 210 + (idx - 210) = idx by omega] using h
        · by_cases h4 : idx < 350
          · have h := decode_check_4 ⟨idx - 280, by omega⟩
            simpa only [show 280 + (idx - 280) = idx by omega] using h
          · have h := decode_check_5 ⟨idx - 350, by omega⟩
            simpa only [show 350 + (idx - 350) = idx by omega] using h

end CommitGolfCandidate
