import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the r=2 packed submission images.
Uses O(1) periodic block deduplication on `ArtifactEncoding.Packed`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨2438289632, 8669633152⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 6733261056, 6867478784, 11162446080⟩ := rfl

theorem commit_dataBase : dataBase (submission.image .commit) = 68719476096 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem opening_dataBase : dataBase (submission.image .opening) = 68719475968 := by
  simp only [submission, MoonArtifact.submission, dataBase, ArtifactEncoding.length_decode, MEMORY_BYTES]
  decide

theorem check_dataBase : dataBase (submission.image .check) = 68719475968 := by
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

private theorem packed_get_congr {n : Nat} (p : ArtifactEncoding.Packed n)
    {a b : Fin n} (h : a.val = b.val) :
    p.get 32 a = p.get 32 b :=
  congrArg (p.get 32) (Fin.ext h)

private def pick8 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : Nat → α
  | 0 => p0 | 1 => p1 | 2 => p2 | 3 => p3
  | 4 => p4 | 5 => p5 | 6 => p6 | _ => p7

private theorem pick8_0 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 0 = p0 := rfl
private theorem pick8_1 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 1 = p1 := rfl
private theorem pick8_2 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 2 = p2 := rfl
private theorem pick8_3 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 3 = p3 := rfl
private theorem pick8_4 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 4 = p4 := rfl
private theorem pick8_5 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 5 = p5 := rfl
private theorem pick8_6 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 6 = p6 := rfl
private theorem pick8_7 {α : Type} (p0 p1 p2 p3 p4 p5 p6 p7 : α) : pick8 p0 p1 p2 p3 p4 p5 p6 p7 7 = p7 := rfl

private theorem packed_get_join8 {S : Nat}
    (p0 p1 p2 p3 p4 p5 p6 p7 : ArtifactEncoding.Packed S)
    (i : Nat) (hi : i < 8 * S) :
    (@ArtifactEncoding.Packed.join (S + S + (S + S)) (S + S + (S + S))
      (@ArtifactEncoding.Packed.join (S + S) (S + S)
        (@ArtifactEncoding.Packed.join S S p0 p1)
        (@ArtifactEncoding.Packed.join S S p2 p3))
      (@ArtifactEncoding.Packed.join (S + S) (S + S)
        (@ArtifactEncoding.Packed.join S S p4 p5)
        (@ArtifactEncoding.Packed.join S S p6 p7))).get 32 ⟨i, by omega⟩ =
    (pick8 p0 p1 p2 p3 p4 p5 p6 p7 (i / S)).get 32 ⟨i % S, Nat.mod_lt i (by omega)⟩ := by
  have hS : 0 < S := by omega
  have hq : i / S < 8 := Nat.div_lt_of_lt_mul (by omega)
  have hmod : i % S < S := Nat.mod_lt i hS
  have hdiv : S * (i / S) + i % S = i := Nat.div_add_mod i S
  generalize hqv : i / S = q at hq hdiv ⊢
  interval_cases q
  · rw [pick8_0,
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_1,
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_2,
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_3,
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_4,
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_5,
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_6,
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_7,
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega),
        ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)

/-! ### Embedded Data Table Verification -/

def packedDword {n : Nat} (p : ArtifactEncoding.Packed n) (off : Nat) (_h : off + 8 ≤ n) : Word :=
  BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (if hj : off + j < n then (p.get 8 ⟨off + j, hj⟩).toNat else 0) * 2 ^ (8 * j))

theorem commitData_dword_0 (i : Fin 20) :
    packedDword MoonArtifact.commitData (32 * i.val) (by omega) =
      BitVec.ofNat 64 (levelBase (i.val + 2)) := by
  revert i; decide

theorem commitData_dword_1 (i : Fin 20) :
    packedDword MoonArtifact.commitData (32 * i.val + 8) (by omega) =
      BitVec.ofNat 64 (levelBase (i.val + 3)) := by
  revert i; decide

theorem commitData_dword_2 (i : Fin 20) :
    packedDword MoonArtifact.commitData (32 * i.val + 16) (by omega) =
      BitVec.ofNat 64 (levelSize (i.val + 2) / 2) := by
  revert i; decide

theorem commitData_dword_3 (i : Fin 20) :
    packedDword MoonArtifact.commitData (32 * i.val + 24) (by omega) =
      BitVec.ofNat 64 (levelSize (i.val + 2) % 2) := by
  revert i; decide

theorem openingData_dword_0 (l : Fin 24) :
    packedDword MoonArtifact.openingData (32 * l.val) (by omega) =
      BitVec.ofNat 64 (levelBase l.val) := by
  revert l; decide

theorem openingData_dword_1 (l : Fin 24) :
    packedDword MoonArtifact.openingData (32 * l.val + 8) (by omega) =
      BitVec.ofNat 64 (levelSize l.val) := by
  revert l; decide

theorem openingData_dword_2 (l : Fin 24) :
    packedDword MoonArtifact.openingData (32 * l.val + 16) (by omega) =
      BitVec.ofNat 64 (capMarkOff l.val) := by
  revert l; decide

theorem openingData_dword_3 (l : Fin 24) :
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

/-! ### Fast Hierarchical Unwrapper for `MoonArtifact.commitCode` -/

private theorem get_commitCode_to_commitCode_2_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 32768) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_0.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_2_1 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 61667) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_1.get 32 ⟨idx - 32768, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_1_to_commitCode_1_8 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 4096) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_8.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_1_to_commitCode_1_9 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 8192) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_9.get 32 ⟨idx - 4096, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_1_to_commitCode_1_10 (idx : Nat) (hlo : 8192 ≤ idx) (hhi : idx < 12288) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_10.get 32 ⟨idx - 8192, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_1_to_commitCode_1_11 (idx : Nat) (hlo : 12288 ≤ idx) (hhi : idx < 16384) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_11.get 32 ⟨idx - 12288, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_1_to_commitCode_1_12 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 20480) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_12.get 32 ⟨idx - 16384, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_1_to_commitCode_1_13 (idx : Nat) (hlo : 20480 ≤ idx) (hhi : idx < 24576) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_13.get 32 ⟨idx - 20480, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_1_to_commitCode_1_14 (idx : Nat) (hlo : 24576 ≤ idx) (hhi : idx < 28672) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_14.get 32 ⟨idx - 24576, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_1_to_commitCode_1_15 (idx : Nat) (hlo : 28672 ≤ idx) (hhi : idx < 28899) :
    MoonArtifact.commitCode_2_1.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_15.get 32 ⟨idx - 28672, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 4096) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_0.get 32 ⟨idx - 0, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_1 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 8192) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_1.get 32 ⟨idx - 4096, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 1 := by omega
  rw [hqd, pick8_1]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_2 (idx : Nat) (hlo : 8192 ≤ idx) (hhi : idx < 12288) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_2.get 32 ⟨idx - 8192, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 2 := by omega
  rw [hqd, pick8_2]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_3 (idx : Nat) (hlo : 12288 ≤ idx) (hhi : idx < 16384) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_3.get 32 ⟨idx - 12288, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 3 := by omega
  rw [hqd, pick8_3]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_4 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 20480) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_4.get 32 ⟨idx - 16384, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 4 := by omega
  rw [hqd, pick8_4]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_5 (idx : Nat) (hlo : 20480 ≤ idx) (hhi : idx < 24576) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_5.get 32 ⟨idx - 20480, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 5 := by omega
  rw [hqd, pick8_5]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_6 (idx : Nat) (hlo : 24576 ≤ idx) (hhi : idx < 28672) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_6.get 32 ⟨idx - 24576, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 6 := by omega
  rw [hqd, pick8_6]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_7 (idx : Nat) (hlo : 28672 ≤ idx) (hhi : idx < 32768) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_7.get 32 ⟨idx - 28672, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 7 := by omega
  rw [hqd, pick8_7]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_8 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 36864) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_8.get 32 ⟨idx - 32768, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_8 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_9 (idx : Nat) (hlo : 36864 ≤ idx) (hhi : idx < 40960) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_9.get 32 ⟨idx - 36864, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_9 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_10 (idx : Nat) (hlo : 40960 ≤ idx) (hhi : idx < 45056) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_10.get 32 ⟨idx - 40960, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_10 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_11 (idx : Nat) (hlo : 45056 ≤ idx) (hhi : idx < 49152) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_11.get 32 ⟨idx - 45056, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_11 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_12 (idx : Nat) (hlo : 49152 ≤ idx) (hhi : idx < 53248) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_12.get 32 ⟨idx - 49152, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_12 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_13 (idx : Nat) (hlo : 53248 ≤ idx) (hhi : idx < 57344) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_13.get 32 ⟨idx - 53248, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_13 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_14 (idx : Nat) (hlo : 57344 ≤ idx) (hhi : idx < 61440) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_14.get 32 ⟨idx - 57344, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_14 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_15 (idx : Nat) (hlo : 61440 ≤ idx) (hhi : idx < 61667) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_15.get 32 ⟨idx - 61440, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  rw [get_commitCode_2_1_to_commitCode_1_15 (idx - 32768) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

/-! ### Commit Program: Constant-Body Repeating Bulk Loops (O(1) Periodic Block Dedup) -/

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

private abbrev randPair_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865643358340941163446270751578390663268940571533112845134541861184991772892350385846498384999493705875223589124882700497246931860205577226074421326059861642867266596390610781429280122821368267815576475587381753083197657510123700016009312751329356524006068573038977222226422360596926039261940882232252498784667368251684788966845983359634162452464663566859808406056209488454305856588338334587945327095908791954406118314960671104388782472078695239105957026330177834613926539588250814899300416883086510197270839185521923652429699840171167812568529796894727786068470785631770075567029052133108972775043163186595091

private theorem randPair_chunk64_p1 (r : Fin 64) :
    randPair_c64_p1.get 32 r = randPairWord ((r.val + 1) % 2) := by
  revert r; decide

private theorem randPair_blk512_p1 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_1.get 32 ⟨r, hr⟩ = randPairWord ((r + 1) % 2) := by
  have h8 := packed_get_join8 (S := 64) randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_1 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_1, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_2, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_3, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_4, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_5, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_6, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_7, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)

private theorem randPair_bnd64_0 (i : Fin 47) :
    (ArtifactEncoding.Packed.chunk 64 865643358340941163446270751578390663268940571533112845134541861184991772892350385846498384999493705875223589124882700497246931860205577226074421326059861642867266596390610781429280122821368267815576475587381753083197657510123700016009312751329356524006068573038977222226422360596926039261940882232252498784667368251684788966845983359634162452464663566859808406056209488454305856588338334587945327095908791954406118314960671104388782472078695239103458036183446057532387798866485385378774222736189990173833335411686642819058852473139088749243000599204003977827080063665408780689561758738870021976999104591758355).get 32 ⟨17 + i.val, by omega⟩ =
      randPairWord ((0 + i.val) % 2) := by
  revert i; decide

private theorem randPair_bnd512_0 (r : Nat) (hlo : 17 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_0.get 32 ⟨r, by omega⟩ = randPairWord ((0 + r - 17) % 2) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865643358340941163446270751578390663268940571533112845134541861184991772892350385846498384999493705875223589124882700497246931860205577226074421326059861642867266596390610781429280122821368267815576475587381753083197657510123700016009312751329356524006068573038977222226422360596926039261940882232252498784667368251684788966845983359634162452464663566859808406056209488454305856588338334587945327095908791954406118314960671104388782472078695239103458036183446057532387798866485385378774222736189990173833335411686642819058852473139088749243000599204003977827080063665408780689561758738870021976999104591758355) randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 randPair_c64_p1 r (by omega)
  have hdef : MoonArtifact.commitCode_0_0 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865643358340941163446270751578390663268940571533112845134541861184991772892350385846498384999493705875223589124882700497246931860205577226074421326059861642867266596390610781429280122821368267815576475587381753083197657510123700016009312751329356524006068573038977222226422360596926039261940882232252498784667368251684788966845983359634162452464663566859808406056209488454305856588338334587945327095908791954406118314960671104388782472078695239103458036183446057532387798866485385378774222736189990173833335411686642819058852473139088749243000599204003977827080063665408780689561758738870021976999104591758355) randPair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p1 randPair_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := randPair_bnd64_0 ⟨r % 64 - 17, by omega⟩
    dsimp only at h
    have heq1 : 17 + (r % 64 - 17) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 17)) % 2 = (0 + r - 17) % 2 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_2, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_3, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_4, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_5, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_6, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_7, randPair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)

private theorem randPair_bnd4096_0 (r : Nat) (hlo : 17 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_0.get 32 ⟨r, by omega⟩ = randPairWord ((0 + r - 17) % 2) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 r (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_bnd512_0 (r % 512) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_1 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_2 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_3 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_4 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_5 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_6 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_7 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p1 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)

private theorem randPair_bnd64_64 (i : Fin 17) :
    (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131).get 32 ⟨0 + i.val, by omega⟩ =
      randPairWord ((4079 + i.val) % 2) := by
  revert i; decide

private theorem randPair_bnd512_8 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 17) :
    MoonArtifact.commitCode_0_8.get 32 ⟨r, by omega⟩ = randPairWord ((4096 + r - 17) % 2) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) r (by omega)
  have hdef : MoonArtifact.commitCode_0_8 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := randPair_bnd64_64 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (4079 + (r % 64 - 0)) % 2 = (4096 + r - 17) % 2 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem randPair_bnd4096_1 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 17) :
    MoonArtifact.commitCode_1_1.get 32 ⟨r, by omega⟩ = randPairWord ((4096 + r - 17) % 2) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 r (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_bnd512_8 (r % 512) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (17 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (17 + 2 * k + j) (by omega)
    (randPairWord j) hpc _ (randPairInstr j) (decode_randPairWord ⟨j, hj⟩)
  have hg_lo : 0 ≤ (17 + 2 * k + j) / 4096 := by omega
  have hg_hi : (17 + 2 * k + j) / 4096 ≤ 1 := by omega
  generalize hgv : (17 + 2 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_0 (17 + 2 * k + j) (by omega) (by omega)]
    rw [randPair_bnd4096_0 (17 + 2 * k + j - 0) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_1 (17 + 2 * k + j) (by omega) (by omega)]
    rw [randPair_bnd4096_1 (17 + 2 * k + j - 4096) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)

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

private abbrev leaf0_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219

private theorem leaf0_chunk64_p0 (r : Fin 64) :
    leaf0_c64_p0.get 32 r = leaf0Word ((r.val + 0) % 3) := by
  revert r; decide

private abbrev leaf0_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043

private theorem leaf0_chunk64_p1 (r : Fin 64) :
    leaf0_c64_p1.get 32 r = leaf0Word ((r.val + 1) % 3) := by
  revert r; decide

private abbrev leaf0_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579

private theorem leaf0_chunk64_p2 (r : Fin 64) :
    leaf0_c64_p2.get 32 r = leaf0Word ((r.val + 2) % 3) := by
  revert r; decide

private theorem leaf0_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_9.get 32 ⟨r, hr⟩ = leaf0Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_9 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_1, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_2, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_3, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_4, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_5, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_6, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_7, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)

private theorem leaf0_blk512_p1 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_11.get 32 ⟨r, hr⟩ = leaf0Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_11 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_1, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_2, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_3, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_4, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_5, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_6, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_7, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)

private theorem leaf0_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_10.get 32 ⟨r, hr⟩ = leaf0Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_10 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_1, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_2, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_3, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_4, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_5, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_6, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_7, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)

private theorem leaf0_grp4096_p0 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_3.get 32 ⟨r, hr⟩ = leaf0Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 r hr
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_24 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_25 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_26 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_27 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_28 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_29 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_30 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_31 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_grp4096_p2 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_2.get 32 ⟨r, hr⟩ = leaf0Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 r hr
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_16 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_17 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_18 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_19 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_20 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_21 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_22 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_23 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_bnd64_64 (i : Fin 35) :
    (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131).get 32 ⟨29 + i.val, by omega⟩ =
      leaf0Word ((0 + i.val) % 3) := by
  revert i; decide

private theorem leaf0_bnd512_8 (r : Nat) (hlo : 29 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_8.get 32 ⟨r, by omega⟩ = leaf0Word ((4096 + r - 4125) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131) leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 r (by omega)
  have hdef : MoonArtifact.commitCode_0_8 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821901447697629567181142785461286623146269802013133817649449602664430340034293730650419178205513798418819515537238913114369777373390222475130555956080944038250873020943061035289393682608769772555709154744492856292176428748710987983036631384265588871459985201874969233983434131834131) leaf0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf0_bnd64_64 ⟨r % 64 - 29, by omega⟩
    dsimp only at h
    have heq1 : 29 + (r % 64 - 29) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 29)) % 3 = (4096 + r - 4125) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_2, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_3, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_4, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_5, leaf0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_6, leaf0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)
  · rw [pick8_7, leaf0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf0Word (by dsimp only; omega)

private theorem leaf0_bnd4096_1 (r : Nat) (hlo : 29 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_1.get 32 ⟨r, by omega⟩ = leaf0Word ((4096 + r - 4125) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 r (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_bnd512_8 (r % 512) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_9 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_10 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_11 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_12 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_13 = MoonArtifact.commitCode_0_10 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_14 = MoonArtifact.commitCode_0_11 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_15 = MoonArtifact.commitCode_0_9 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_bnd64_256 (i : Fin 29) :
    (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627).get 32 ⟨0 + i.val, by omega⟩ =
      leaf0Word ((12259 + i.val) % 3) := by
  revert i; decide

private theorem leaf0_bnd512_32 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 29) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = leaf0Word ((16384 + r - 4125) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131) (ArtifactEncoding.Packed.chunk 64 865467120727773686283491452108367008307497078519435085739400620816703032798400985281120802439184467591623175330869133650445321199986579992878756064747313401265241845285057674253498038692133748609401083884444299130320622576238913128533198328329140998743689395554502633754355794762624369050772293816435357173752551695083289710670807335086997111907031931425170214889747137003919668783778481603138610244432853267625702868433392070203279031512056445844586697845511258788115936773073211546379877142328767601578771623825931110020868592477819875008189279378391188862096661224026106315063463019514510652503544465195123) (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318294483527242574669673236250288345192960760905798375502901669179194721440055592450647691510501488661529835745562808596463397663278773955148436436570730324366763492128760131720530034228379546961738657979679945669212771831669963323663296823292031361347205424585260072494692964563651808002046710076009646446919797639576662209231448783119523093095838166610024210451473335381722387) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131) (ArtifactEncoding.Packed.chunk 64 865467120727773686283491452108367008307497078519435085739400620816703032798400985281120802439184467591623175330869133650445321199986579992878756064747313401265241845285057674253498038692133748609401083884444299130320622576238913128533198328329140998743689395554502633754355794762624369050772293816435357173752551695083289710670807335086997111907031931425170214889747137003919668783778481603138610244432853267625702868433392070203279031512056445844586697845511258788115936773073211546379877142328767601578771623825931110020868592477819875008189279378391188862096661224026106315063463019514510652503544465195123) (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318294483527242574669673236250288345192960760905798375502901669179194721440055592450647691510501488661529835745562808596463397663278773955148436436570730324366763492128760131720530034228379546961738657979679945669212771831669963323663296823292031361347205424585260072494692964563651808002046710076009646446919797639576662209231448783119523093095838166610024210451473335381722387) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131) r (by omega)
  have hdef : MoonArtifact.commitCode_0_32 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865467120727773686283491452108367008307497078519435085739400620816703032798400985281120802439184467591623175330869133650445321199986579992878756064747313401265241845285057674253498038692133748609401083884444299130320622576238913128533198328329140998743689395554502633754355794762624369050772293816435357173752551695083289710670807335086997111907031931425170214889747137003919668783778481603138610244432853267625702868433392070203279031512056445844586697845511258788115936773073211546379877142328767601578771623825931110020868592477819875008189279378391188862096661224026106315063463019514510652503544465195123) (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318294483527242574669673236250288345192960760905798375502901669179194721440055592450647691510501488661529835745562808596463397663278773955148436436570730324366763492128760131720530034228379546961738657979679945669212771831669963323663296823292031361347205424585260072494692964563651808002046710076009646446919797639576662209231448783119523093095838166610024210451473335381722387))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131) (ArtifactEncoding.Packed.chunk 64 865467120727773686283491452108367008307497078519435085739400620816703032798400985281120802439184467591623175330869133650445321199986579992878756064747313401265241845285057674253498038692133748609401083884444299130320622576238913128533198328329140998743689395554502633754355794762624369050772293816435357173752551695083289710670807335086997111907031931425170214889747137003919668783778481603138610244432853267625702868433392070203279031512056445844586697845511258788115936773073211546379877142328767601578771623825931110020868592477819875008189279378391188862096661224026106315063463019514510652503544465195123)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318294483527242574669673236250288345192960760905798375502901669179194721440055592450647691510501488661529835745562808596463397663278773955148436436570730324366763492128760131720530034228379546961738657979679945669212771831669963323663296823292031361347205424585260072494692964563651808002046710076009646446919797639576662209231448783119523093095838166610024210451473335381722387) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf0_bnd64_256 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (12259 + (r % 64 - 0)) % 3 = (16384 + r - 4125) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf0_bnd4096_4 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 29) :
    MoonArtifact.commitCode_1_4.get 32 ⟨r, by omega⟩ = leaf0Word ((16384 + r - 4125) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 r (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_bnd512_32 (r % 512) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 4096) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4125 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (4125 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  have hg_lo : 1 ≤ (4125 + 3 * k + j) / 4096 := by omega
  have hg_hi : (4125 + 3 * k + j) / 4096 ≤ 4 := by omega
  generalize hgv : (4125 + 3 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_1 (4125 + 3 * k + j) (by omega) (by omega)]
    rw [leaf0_bnd4096_1 (4125 + 3 * k + j - 4096) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_2 (4125 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_2 = MoonArtifact.commitCode_1_2 := rfl
    rw [hgrp, leaf0_grp4096_p2 (4125 + 3 * k + j - 8192) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_3 (4125 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_3 = MoonArtifact.commitCode_1_3 := rfl
    rw [hgrp, leaf0_grp4096_p0 (4125 + 3 * k + j - 12288) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_4 (4125 + 3 * k + j) (by omega) (by omega)]
    rw [leaf0_bnd4096_4 (4125 + 3 * k + j - 16384) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)

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

private abbrev leaf12Pair_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575730149412029178065080716896200375655512687519430968582245267153544972411501945017486743012014396375092429333982281933043736953912743293720744727956209674102429249570443529448108086642248996921765154819041109190341701683566912511982742037456680073302016028411459413954407452918233901778062022401217866061985873927748936829474797657983128483289621452080489644684849745839415178494382314179798345428973048635993217390862169328942540633744524790261173480103306227240184496403894781478712131293342667329372570949683940741451147771439967998336258418362468857714577182507224052122650131

private theorem leaf12Pair_chunk64_p1 (r : Fin 64) :
    leaf12Pair_c64_p1.get 32 r = leaf12PairWord ((r.val + 1) % 12) := by
  revert r; decide

private abbrev leaf12Pair_c64_p5 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865467120727773686283491452108367008307497078519435085739400620816703032798400985281120802439184467591623175330869133650445321199986579992878756064747313401265241845285057674253498038692133748609401083884444299130320622576238913128533198328329140998743689395554502633754355794762624369050772293816435357173752551695083289710670807335086997111907031931425170214889747137003919668783778481603138610244432853267625702868433392070203279031512056445844586697845511258788115936773073211546379877142328767601578771623825931110020868592477819875008189279378391188862096661224026106315063463019514510652503544465195123

private theorem leaf12Pair_chunk64_p5 (r : Fin 64) :
    leaf12Pair_c64_p5.get 32 r = leaf12PairWord ((r.val + 5) % 12) := by
  revert r; decide

private abbrev leaf12Pair_c64_p9 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318294483527242574669673236250288345192960760905798375502901669179194721440055592450647691510501488661529835745562808596463397663278773955148436436570730324366763492128760131720530034228379546961738657979679945669212771831669963323663296823292031361347205424585260072494692964563651808002046710076009646446919797639576662209231448783119523093095838166610024210451473335381722387

private theorem leaf12Pair_chunk64_p9 (r : Fin 64) :
    leaf12Pair_c64_p9.get 32 r = leaf12PairWord ((r.val + 9) % 12) := by
  revert r; decide

private theorem leaf12Pair_blk512_p1 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_34.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 1) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 r hr
  have hdef : MoonArtifact.commitCode_0_34 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p1 leaf12Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p9 leaf12Pair_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p5 leaf12Pair_c64_p9) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p1 leaf12Pair_c64_p5))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_blk512_p5 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_33.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 5) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 r hr
  have hdef : MoonArtifact.commitCode_0_33 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p5 leaf12Pair_c64_p9) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p1 leaf12Pair_c64_p5)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p9 leaf12Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p5 leaf12Pair_c64_p9))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_blk512_p9 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_35.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 9) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_35 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p9 leaf12Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p5 leaf12Pair_c64_p9)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p1 leaf12Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p9 leaf12Pair_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_grp4096_p1 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_5.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 1) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 r hr
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_40 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_41 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_42 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_43 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_44 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_45 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_46 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_47 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_grp4096_p5 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_6.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 5) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 r hr
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_48 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_49 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_50 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_51 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_52 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_53 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_54 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_55 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_grp4096_p9 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_7.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 9) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 r hr
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_56 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_57 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_58 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_59 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_60 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_61 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_62 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_63 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_bnd64_256 (i : Fin 25) :
    (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627).get 32 ⟨39 + i.val, by omega⟩ =
      leaf12PairWord ((0 + i.val) % 12) := by
  revert i; decide

private theorem leaf12Pair_bnd512_32 (r : Nat) (hlo : 39 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = leaf12PairWord ((16384 + r - 16423) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627) leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 leaf12Pair_c64_p5 leaf12Pair_c64_p9 leaf12Pair_c64_p1 r (by omega)
  have hdef : MoonArtifact.commitCode_0_32 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 1264858415736187346245100373183308827888013137943537357236106531228979578378697127827303605763373837389402670187977790017934399535915908557703251644982215194581517473593233892153332291191156643307541713965057833839553398753375116669888196318301881480509555507030458648670136114409741940799734119201040084064256338654546821114423165313591296521744787368867629672958426915234852517779155162746479395131092120510466403664781714719363381908223378597662138054670892318765064102140962896010253663905921923022009488269379074496721936320645920176689315116949949072126711316286768444375421952630436118177763018486584434820627) leaf12Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p5 leaf12Pair_c64_p9)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p1 leaf12Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p9 leaf12Pair_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf12Pair_bnd64_256 ⟨r % 64 - 39, by omega⟩
    dsimp only at h
    have heq1 : 39 + (r % 64 - 39) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 39)) % 12 = (16384 + r - 16423) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p9 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_bnd4096_4 (r : Nat) (hlo : 39 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_4.get 32 ⟨r, by omega⟩ = leaf12PairWord ((16384 + r - 16423) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 r (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_bnd512_32 (r % 512) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_33 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_34 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_35 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_36 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_37 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf12Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_38 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf12Pair_blk512_p9 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_39 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf12Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_bnd64_640 (i : Fin 39) :
    (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091).get 32 ⟨0 + i.val, by omega⟩ =
      leaf12PairWord ((24537 + i.val) % 12) := by
  revert i; decide

private theorem leaf12Pair_bnd512_80 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 39) :
    MoonArtifact.commitCode_0_80.get 32 ⟨r, by omega⟩ = leaf12PairWord ((40960 + r - 16423) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475) (ArtifactEncoding.Packed.chunk 64 255447020792392060713696978022541310753591158490242568159521131014011284605726979136010845181911793407689492339018085071583526758796884610775628446079126294961282910948528864134364924522708894570060354677485083236015704687921507260310615114015745206619242162570617484282186116202827738182505068337870643258280098912948410456691308036662718160082588648522177279539779145481052218138172289373859805336788940119222453068676933326709867627291699847543304239326941618484388435008152569167285996256639679835469121874119919786710824950828495709715328945652688657815720956257005578091767179725542660570778017268358795626003) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023421998954139762072904335033324011640431684322013689286759317078748454533325826287719820090474700736982848453110383660093128383110931232458259923516095968298488782373919630595890417016425009227369189742482285589581444800623485382215194188456607706795261249459195563248855360450389708841084718474539226317959364908769955496829589069516618996851468272781758733610640633274437665001324748674955147580331860546183128687116442200694491469753274079492324401085798922649841558356083) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475) (ArtifactEncoding.Packed.chunk 64 255447020792392060713696978022541310753591158490242568159521131014011284605726979136010845181911793407689492339018085071583526758796884610775628446079126294961282910948528864134364924522708894570060354677485083236015704687921507260310615114015745206619242162570617484282186116202827738182505068337870643258280098912948410456691308036662718160082588648522177279539779145481052218138172289373859805336788940119222453068676933326709867627291699847543304239326941618484388435008152569167285996256639679835469121874119919786710824950828495709715328945652688657815720956257005578091767179725542660570778017268358795626003) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023421998954139762072904335033324011640431684322013689286759317078748454533325826287719820090474700736982848453110383660093128383110931232458259923516095968298488782373919630595890417016425009227369189742482285589581444800623485382215194188456607706795261249459195563248855360450389708841084718474539226317959364908769955496829589069516618996851468272781758733610640633274437665001324748674955147580331860546183128687116442200694491469753274079492324401085798922649841558356083) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475) r (by omega)
  have hdef : MoonArtifact.commitCode_0_80 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020792392060713696978022541310753591158490242568159521131014011284605726979136010845181911793407689492339018085071583526758796884610775628446079126294961282910948528864134364924522708894570060354677485083236015704687921507260310615114015745206619242162570617484282186116202827738182505068337870643258280098912948410456691308036662718160082588648522177279539779145481052218138172289373859805336788940119222453068676933326709867627291699847543304239326941618484388435008152569167285996256639679835469121874119919786710824950828495709715328945652688657815720956257005578091767179725542660570778017268358795626003) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023421998954139762072904335033324011640431684322013689286759317078748454533325826287719820090474700736982848453110383660093128383110931232458259923516095968298488782373919630595890417016425009227369189742482285589581444800623485382215194188456607706795261249459195563248855360450389708841084718474539226317959364908769955496829589069516618996851468272781758733610640633274437665001324748674955147580331860546183128687116442200694491469753274079492324401085798922649841558356083))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475) (ArtifactEncoding.Packed.chunk 64 255447020792392060713696978022541310753591158490242568159521131014011284605726979136010845181911793407689492339018085071583526758796884610775628446079126294961282910948528864134364924522708894570060354677485083236015704687921507260310615114015745206619242162570617484282186116202827738182505068337870643258280098912948410456691308036662718160082588648522177279539779145481052218138172289373859805336788940119222453068676933326709867627291699847543304239326941618484388435008152569167285996256639679835469121874119919786710824950828495709715328945652688657815720956257005578091767179725542660570778017268358795626003)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023421998954139762072904335033324011640431684322013689286759317078748454533325826287719820090474700736982848453110383660093128383110931232458259923516095968298488782373919630595890417016425009227369189742482285589581444800623485382215194188456607706795261249459195563248855360450389708841084718474539226317959364908769955496829589069516618996851468272781758733610640633274437665001324748674955147580331860546183128687116442200694491469753274079492324401085798922649841558356083) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf12Pair_bnd64_640 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (24537 + (r % 64 - 0)) % 12 = (40960 + r - 16423) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf12Pair_bnd4096_10 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 39) :
    MoonArtifact.commitCode_1_10.get 32 ⟨r, by omega⟩ = leaf12PairWord ((40960 + r - 16423) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87 r (by omega)
  have hdef : MoonArtifact.commitCode_1_10 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_bnd512_80 (r % 512) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16423 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (16423 + 12 * k + j) (by omega)
    (leaf12PairWord j) hpc _ (leaf12PairInstr j) (decode_leaf12PairWord ⟨j, hj⟩)
  have hg_lo : 4 ≤ (16423 + 12 * k + j) / 4096 := by omega
  have hg_hi : (16423 + 12 * k + j) / 4096 ≤ 10 := by omega
  generalize hgv : (16423 + 12 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_4 (16423 + 12 * k + j) (by omega) (by omega)]
    rw [leaf12Pair_bnd4096_4 (16423 + 12 * k + j - 16384) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_5 (16423 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_5 = MoonArtifact.commitCode_1_5 := rfl
    rw [hgrp, leaf12Pair_grp4096_p1 (16423 + 12 * k + j - 20480) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_6 (16423 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_6 = MoonArtifact.commitCode_1_6 := rfl
    rw [hgrp, leaf12Pair_grp4096_p5 (16423 + 12 * k + j - 24576) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_7 (16423 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_7 = MoonArtifact.commitCode_1_7 := rfl
    rw [hgrp, leaf12Pair_grp4096_p9 (16423 + 12 * k + j - 28672) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_8 (16423 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_8 = MoonArtifact.commitCode_1_5 := rfl
    rw [hgrp, leaf12Pair_grp4096_p1 (16423 + 12 * k + j - 32768) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_9 (16423 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_9 = MoonArtifact.commitCode_1_6 := rfl
    rw [hgrp, leaf12Pair_grp4096_p5 (16423 + 12 * k + j - 36864) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_10 (16423 + 12 * k + j) (by omega) (by omega)]
    rw [leaf12Pair_bnd4096_10 (16423 + 12 * k + j - 40960) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)

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

private abbrev leaf3Pair_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020792392060713696978022541310753591158490242568159521131014011284605726979136010845181911793407689492339018085071583526758796884610775628446079126294961282910948528864134364924522708894570060354677485083236015704687921507260310615114015745206619242162570617484282186116202827738182505068337870643258280098912948410456691308036662718160082588648522177279539779145481052218138172289373859805336788940119222453068676933326709867627291699847543304239326941618484388435008152569167285996256639679835469121874119919786710824950828495709715328945652688657815720956257005578091767179725542660570778017268358795626003

private theorem leaf3Pair_chunk64_p1 (r : Fin 64) :
    leaf3Pair_c64_p1.get 32 r = leaf3PairWord ((r.val + 1) % 6) := by
  revert r; decide

private abbrev leaf3Pair_c64_p3 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922044152797841304491023548354859906490042645846014703011643971222251357571349981399274014992600439082480917540908467378856153866541239304363355032627944695579282310476702512028291562022721791285317619869724416714851765038225535638889082035153893748993671116683064434859621647185187119219632156405831545911555903277380142470211791671731369459513693327396722187051766358729303886707690209661133113851761425546535722265068204779671658776907017656637997890398434449145554752280117222396465122178466094683236746179493967493095269404875930422862460391121920886292296931225917766627034971571475

private theorem leaf3Pair_chunk64_p3 (r : Fin 64) :
    leaf3Pair_c64_p3.get 32 r = leaf3PairWord ((r.val + 3) % 6) := by
  revert r; decide

private abbrev leaf3Pair_c64_p5 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023421998954139762072904335033324011640431684322013689286759317078748454533325826287719820090474700736982848453110383660093128383110931232458259923516095968298488782373919630595890417016425009227369189742482285589581444800623485382215194188456607706795261249459195563248855360450389708841084718474539226317959364908769955496829589069516618996851468272781758733610640633274437665001324748674955147580331860546183128687116442200694491469753274079492324401085798922649841558356083

private theorem leaf3Pair_chunk64_p5 (r : Fin 64) :
    leaf3Pair_c64_p5.get 32 r = leaf3PairWord ((r.val + 5) % 6) := by
  revert r; decide

private theorem leaf3Pair_blk512_p1 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_81.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 1) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 r hr
  have hdef : MoonArtifact.commitCode_0_81 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p1 leaf3Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p3 leaf3Pair_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p5 leaf3Pair_c64_p3) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p1 leaf3Pair_c64_p5))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_blk512_p3 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_82.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 3) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_82 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p3 leaf3Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p5 leaf3Pair_c64_p3)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p1 leaf3Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p3 leaf3Pair_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_blk512_p5 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_83.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 5) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 r hr
  have hdef : MoonArtifact.commitCode_0_83 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p5 leaf3Pair_c64_p3) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p1 leaf3Pair_c64_p5)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p3 leaf3Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p5 leaf3Pair_c64_p3))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_grp4096_p1 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_12.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 1) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_96 MoonArtifact.commitCode_0_97 MoonArtifact.commitCode_0_98 MoonArtifact.commitCode_0_99 MoonArtifact.commitCode_0_100 MoonArtifact.commitCode_0_101 MoonArtifact.commitCode_0_102 MoonArtifact.commitCode_0_103 r hr
  have hdef : MoonArtifact.commitCode_1_12 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_96 MoonArtifact.commitCode_0_97) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_98 MoonArtifact.commitCode_0_99)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_100 MoonArtifact.commitCode_0_101) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_102 MoonArtifact.commitCode_0_103))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_96 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_97 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_98 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_99 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_100 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_101 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_102 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_103 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_grp4096_p3 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_11.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 3) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_88 MoonArtifact.commitCode_0_89 MoonArtifact.commitCode_0_90 MoonArtifact.commitCode_0_91 MoonArtifact.commitCode_0_92 MoonArtifact.commitCode_0_93 MoonArtifact.commitCode_0_94 MoonArtifact.commitCode_0_95 r hr
  have hdef : MoonArtifact.commitCode_1_11 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_88 MoonArtifact.commitCode_0_89) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_90 MoonArtifact.commitCode_0_91)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_92 MoonArtifact.commitCode_0_93) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_94 MoonArtifact.commitCode_0_95))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_88 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_89 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_90 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_91 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_92 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_93 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_94 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_95 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_bnd64_640 (i : Fin 15) :
    (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091).get 32 ⟨49 + i.val, by omega⟩ =
      leaf3PairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem leaf3Pair_bnd512_80 (r : Nat) (hlo : 49 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_80.get 32 ⟨r, by omega⟩ = leaf3PairWord ((40960 + r - 41009) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091) leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 leaf3Pair_c64_p1 leaf3Pair_c64_p5 leaf3Pair_c64_p3 r (by omega)
  have hdef : MoonArtifact.commitCode_0_80 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520015546737346030060242171536185172696603135211336122508680461169905921577745088730408722106023422015545883208746200235875889311918966308166102043413860918117649738391524768886645802321235627132680673426709455697668468742232254561664666921543401204677573508713696969403988801424471227045913433855636417718130476327726454893240101818570574686792048908156298509907243353693587991255045015249550952662161185987950421214349396585685883003068342753450486575807083973279504849860787346743903837004931479754250463739454666605626610848209650637066556025862054107797249549731091) leaf3Pair_c64_p3) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p1 leaf3Pair_c64_p5)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p3 leaf3Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p5 leaf3Pair_c64_p3))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf3Pair_bnd64_640 ⟨r % 64 - 49, by omega⟩
    dsimp only at h
    have heq1 : 49 + (r % 64 - 49) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 49)) % 6 = (40960 + r - 41009) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_bnd4096_10 (r : Nat) (hlo : 49 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_10.get 32 ⟨r, by omega⟩ = leaf3PairWord ((40960 + r - 41009) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87 r (by omega)
  have hdef : MoonArtifact.commitCode_1_10 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_bnd512_80 (r % 512) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_81 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_82 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_83 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_84 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_85 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf3Pair_blk512_p3 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_86 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf3Pair_blk512_p5 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_87 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf3Pair_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_bnd64_832 (i : Fin 49) :
    (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299).get 32 ⟨0 + i.val, by omega⟩ =
      leaf3PairWord ((12239 + i.val) % 6) := by
  revert i; decide

private theorem leaf3Pair_bnd512_104 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 49) :
    MoonArtifact.commitCode_0_104.get 32 ⟨r, by omega⟩ = leaf3PairWord ((53248 + r - 41009) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520058734614027647705744159155401499630891640497246539221813522630166583118733945146918353967448186517976214746896195350764119793733124877212513279210761261646293355845920053199632037976652541973194153781192036733941050385847895186587508972331367987450005264137019947304566423548939401990398731219180778816807156949560995201422212630061997331084518370439822136729722844149700376119110493132981244326535321338264172556192250254186573961666920666407042426340447727972900116776745300402375087862467406898699662108981144116476887701743662040507272433720619942140910290075763) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922840828506074033728930604097218116716386328630720587659433692184696413069800487237208779188076049676011104750250651920796902338083094565073478397875111782049028663881213893448537115268475476584615100718653140427907898664080075633021419998914059075612989412276889260695455997256909137363813588093293459669442893308140304227077603444651494890010149803643214620867568682463879320644986753536143518664168594902900584935935075922614853158936428609490890219873444806342648782192963677429210538717766342281950650559254078122168041232783847686446598750736417477717044526762207220242444382962963) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520058734614027647705744159155401499630891640497246539221813522630166583118733945146918353967448186517976214746896195350764119793733124877212513279210761261646293355845920053199632037976652541973194153781192036733941050385847895186587508972331367987450005264137019947304566423548939401990398731219180778816807156949560995201422212630061997331084518370439822136729722844149700376119110493132981244326535321338264172556192250254186573961666920666407042426340447727972900116776745300402375087862467406898699662108981144116476887701743662040507272433720619942140910290075763) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922840828506074033728930604097218116716386328630720587659433692184696413069800487237208779188076049676011104750250651920796902338083094565073478397875111782049028663881213893448537115268475476584615100718653140427907898664080075633021419998914059075612989412276889260695455997256909137363813588093293459669442893308140304227077603444651494890010149803643214620867568682463879320644986753536143518664168594902900584935935075922614853158936428609490890219873444806342648782192963677429210538717766342281950650559254078122168041232783847686446598750736417477717044526762207220242444382962963) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611) r (by omega)
  have hdef : MoonArtifact.commitCode_0_104 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520058734614027647705744159155401499630891640497246539221813522630166583118733945146918353967448186517976214746896195350764119793733124877212513279210761261646293355845920053199632037976652541973194153781192036733941050385847895186587508972331367987450005264137019947304566423548939401990398731219180778816807156949560995201422212630061997331084518370439822136729722844149700376119110493132981244326535321338264172556192250254186573961666920666407042426340447727972900116776745300402375087862467406898699662108981144116476887701743662040507272433720619942140910290075763) (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922840828506074033728930604097218116716386328630720587659433692184696413069800487237208779188076049676011104750250651920796902338083094565073478397875111782049028663881213893448537115268475476584615100718653140427907898664080075633021419998914059075612989412276889260695455997256909137363813588093293459669442893308140304227077603444651494890010149803643214620867568682463879320644986753536143518664168594902900584935935075922614853158936428609490890219873444806342648782192963677429210538717766342281950650559254078122168041232783847686446598750736417477717044526762207220242444382962963))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520058734614027647705744159155401499630891640497246539221813522630166583118733945146918353967448186517976214746896195350764119793733124877212513279210761261646293355845920053199632037976652541973194153781192036733941050385847895186587508972331367987450005264137019947304566423548939401990398731219180778816807156949560995201422212630061997331084518370439822136729722844149700376119110493132981244326535321338264172556192250254186573961666920666407042426340447727972900116776745300402375087862467406898699662108981144116476887701743662040507272433720619942140910290075763)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922840828506074033728930604097218116716386328630720587659433692184696413069800487237208779188076049676011104750250651920796902338083094565073478397875111782049028663881213893448537115268475476584615100718653140427907898664080075633021419998914059075612989412276889260695455997256909137363813588093293459669442893308140304227077603444651494890010149803643214620867568682463879320644986753536143518664168594902900584935935075922614853158936428609490890219873444806342648782192963677429210538717766342281950650559254078122168041232783847686446598750736417477717044526762207220242444382962963) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf3Pair_bnd64_832 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (12239 + (r % 64 - 0)) % 6 = (53248 + r - 41009) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf3Pair_bnd4096_13 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 49) :
    MoonArtifact.commitCode_1_13.get 32 ⟨r, by omega⟩ = leaf3PairWord ((53248 + r - 41009) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111 r (by omega)
  have hdef : MoonArtifact.commitCode_1_13 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_bnd512_104 (r % 512) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (41009 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (41009 + 6 * k + j) (by omega)
    (leaf3PairWord j) hpc _ (leaf3PairInstr j) (decode_leaf3PairWord ⟨j, hj⟩)
  have hg_lo : 10 ≤ (41009 + 6 * k + j) / 4096 := by omega
  have hg_hi : (41009 + 6 * k + j) / 4096 ≤ 13 := by omega
  generalize hgv : (41009 + 6 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_10 (41009 + 6 * k + j) (by omega) (by omega)]
    rw [leaf3Pair_bnd4096_10 (41009 + 6 * k + j - 40960) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_11 (41009 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_11 = MoonArtifact.commitCode_1_11 := rfl
    rw [hgrp, leaf3Pair_grp4096_p3 (41009 + 6 * k + j - 45056) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_12 (41009 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_12 = MoonArtifact.commitCode_1_12 := rfl
    rw [hgrp, leaf3Pair_grp4096_p1 (41009 + 6 * k + j - 49152) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_13 (41009 + 6 * k + j) (by omega) (by omega)]
    rw [leaf3Pair_bnd4096_13 (41009 + 6 * k + j - 53248) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)

def l1CallWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x02060613#32
  | 2 => 0x00000073#32
  | _ => 0#32

def l1CallInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_l1CallWord (j : Fin 3) :
    decodeInstruction (l1CallWord j.val) = some (l1CallInstr j.val) := by
  revert j; decide

private abbrev l1Call_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857171430424922840828506074033728930604097218116716386328630720587659433692184696413069800487237208779188076049676011104750250651920796902338083094565073478397875111782049028663881213893448537115268475476584615100718653140427907898664080075633021419998914059075612989412276889260695455997256909137363813588093293459669442893308140304227077603444651494890010149803643214620867568682463879320644986753536143518664168594902900584935935075922614853158936428609490890219873444806342648782192963677429210538717766342281950650559254078122168041232783847686446598750736417477717044526762207220242444382962963

private theorem l1Call_chunk64_p0 (r : Fin 64) :
    l1Call_c64_p0.get 32 r = l1CallWord ((r.val + 0) % 3) := by
  revert r; decide

private abbrev l1Call_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728665487885728234746256429580127452856582949577300738871822045304555871508755737507322943165885883734078434002239517665808245884695486548239018881365944028487900668812546691691894618442280720718755350223854933551018191614929811124757941351047226391170585145244348001552607800790519608655787756131350161021536070174576559268373685111006412827974354485670511033930631583283553616007365372492776640849165471130270349015518405539259568505900257788851706346619609754628077979055181736019606957233829215101054439549539108273416801844032226105043737313422893210081698754273421914670611

private theorem l1Call_chunk64_p1 (r : Fin 64) :
    l1Call_c64_p1.get 32 r = l1CallWord ((r.val + 1) % 3) := by
  revert r; decide

private abbrev l1Call_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520058734614027647705744159155401499630891640497246539221813522630166583118733945146918353967448186517976214746896195350764119793733124877212513279210761261646293355845920053199632037976652541973194153781192036733941050385847895186587508972331367987450005264137019947304566423548939401990398731219180778816807156949560995201422212630061997331084518370439822136729722844149700376119110493132981244326535321338264172556192250254186573961666920666407042426340447727972900116776745300402375087862467406898699662108981144116476887701743662040507272433720619942140910290075763

private theorem l1Call_chunk64_p2 (r : Fin 64) :
    l1Call_c64_p2.get 32 r = l1CallWord ((r.val + 2) % 3) := by
  revert r; decide

private theorem l1Call_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_107.get 32 ⟨r, hr⟩ = l1CallWord ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_107 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p0 l1Call_c64_p1) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p2 l1Call_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p1 l1Call_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p0 l1Call_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_1, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_2, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_3, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_4, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_5, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_6, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_7, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)

private theorem l1Call_blk512_p1 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_106.get 32 ⟨r, hr⟩ = l1CallWord ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_106 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p1 l1Call_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p0 l1Call_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p2 l1Call_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p1 l1Call_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_1, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_2, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_3, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_4, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_5, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_6, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_7, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)

private theorem l1Call_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_105.get 32 ⟨r, hr⟩ = l1CallWord ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_105 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p2 l1Call_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p1 l1Call_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p0 l1Call_c64_p1) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p2 l1Call_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_1, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_2, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_3, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_4, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_5, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_6, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_7, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)

private theorem l1Call_bnd64_832 (i : Fin 1) :
    (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299).get 32 ⟨63 + i.val, by omega⟩ =
      l1CallWord ((0 + i.val) % 3) := by
  revert i; decide

private theorem l1Call_bnd512_104 (r : Nat) (hlo : 63 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_104.get 32 ⟨r, by omega⟩ = l1CallWord ((53248 + r - 53311) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299) l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 l1Call_c64_p2 l1Call_c64_p0 l1Call_c64_p1 r (by omega)
  have hdef : MoonArtifact.commitCode_0_104 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195883495719985490240063136591947442481855491890123555054382081017727986785960143743086279969279310441062297818560009243197425119659357186920021349682189286038488380970913556645732716899584266368892922601962440643591604659964385262565442618119941716033047315700930721599299571933877395817798981991321863438222704900825202657939537465203789440895218400750494228896744878047071702357003640896453229552177445187851691304004648075395059537932817580231057791404729599455295556419190931724639047550604070378137105258206183906890659126103365930887287972474633697280756545275818843197116805162333586970030968808669299) l1Call_c64_p1) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p2 l1Call_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p1 l1Call_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Call_c64_p0 l1Call_c64_p1))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := l1Call_bnd64_832 ⟨r % 64 - 63, by omega⟩
    dsimp only at h
    have heq1 : 63 + (r % 64 - 63) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 63)) % 3 = (53248 + r - 53311) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_2, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_3, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_4, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_5, l1Call_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_6, l1Call_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)
  · rw [pick8_7, l1Call_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg l1CallWord (by dsimp only; omega)

private theorem l1Call_bnd4096_13 (r : Nat) (hlo : 63 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_13.get 32 ⟨r, by omega⟩ = l1CallWord ((53248 + r - 53311) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111 r (by omega)
  have hdef : MoonArtifact.commitCode_1_13 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Call_bnd512_104 (r % 512) (by omega) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_105 = MoonArtifact.commitCode_0_105 := rfl
    rw [hblk, l1Call_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_106 = MoonArtifact.commitCode_0_106 := rfl
    rw [hblk, l1Call_blk512_p1 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_107 = MoonArtifact.commitCode_0_107 := rfl
    rw [hblk, l1Call_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_108 = MoonArtifact.commitCode_0_105 := rfl
    rw [hblk, l1Call_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_109 = MoonArtifact.commitCode_0_106 := rfl
    rw [hblk, l1Call_blk512_p1 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_110 = MoonArtifact.commitCode_0_107 := rfl
    rw [hblk, l1Call_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_111 = MoonArtifact.commitCode_0_105 := rfl
    rw [hblk, l1Call_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1CallWord (by omega)

private theorem l1Call_bnd64_896 (i : Fin 62) :
    (ArtifactEncoding.Packed.chunk 64 16166270485363883128481367809098153567797458605518823055942671321195417409159725743215744868980478007586138399771646148353309132225517278640932567746397337773301315539303028118758730444343952612688803848935310611045776696018755853430380898945794348940057753364192292728522469252618756195459722410082090319648954073741066464054268563158851343383798244592821740742531988677869507632769906116148694314245664041451808176814620475398637138294706648499962312642467115222984034622729361865024015863362169659178998086383126234181762610107595617927850356623038951010686591312640318256326197045244061238656757806512002218460691).get 32 ⟨0 + i.val, by omega⟩ =
      l1CallWord ((4033 + i.val) % 3) := by
  revert i; decide

private theorem l1Call_bnd512_112 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 62) :
    MoonArtifact.commitCode_0_112.get 32 ⟨r, by omega⟩ = l1CallWord ((57344 + r - 53311) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 16166270485363883128481367809098153567797458605518823055942671321195417409159725743215744868980478007586138399771646148353309132225517278640932567746397337773301315539303028118758730444343952612688803848935310611045776696018755853430380898945794348940057753364192292728522469252618756195459722410082090319648954073741066464054268563158851343383798244592821740742531988677869507632769906116148694314245664041451808176814620475398637138294706648499962312642467115222984034622729361865024015863362169659178998086383126234181762610107595617927850356623038951010686591312640318256326197045244061238656757806512002218460691) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594266352274101783360133553644653483110803992673741747102673841019853610558311441410181084848534288286881814970678290331215513809800344636504997953242083782004841426844555785362903381692548683945986296097963597099587446619911923279654505026589699683075) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) r (by omega)
  have hdef : MoonArtifact.commitCode_0_112 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 16166270485363883128481367809098153567797458605518823055942671321195417409159725743215744868980478007586138399771646148353309132225517278640932567746397337773301315539303028118758730444343952612688803848935310611045776696018755853430380898945794348940057753364192292728522469252618756195459722410082090319648954073741066464054268563158851343383798244592821740742531988677869507632769906116148694314245664041451808176814620475398637138294706648499962312642467115222984034622729361865024015863362169659178998086383126234181762610107595617927850356623038951010686591312640318256326197045244061238656757806512002218460691) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594266352274101783360133553644653483110803992673741747102673841019853610558311441410181084848534288286881814970678290331215513809800344636504997953242083782004841426844555785362903381692548683945986296097963597099587446619911923279654505026589699683075)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := l1Call_bnd64_896 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (4033 + (r % 64 - 0)) % 3 = (57344 + r - 53311) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem l1Call_bnd4096_14 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 62) :
    MoonArtifact.commitCode_1_14.get 32 ⟨r, by omega⟩ = l1CallWord ((57344 + r - 53311) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 r (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Call_bnd512_112 (r % 512) (by omega) (by omega)]
    exact congrArg l1CallWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_l1_bulk (state : MachineState) (k j : Nat) (hk : k < 1365) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (l1CallInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (53311 + 3 * k + j) (by omega)
    (l1CallWord j) hpc _ (l1CallInstr j) (decode_l1CallWord ⟨j, hj⟩)
  have hg_lo : 13 ≤ (53311 + 3 * k + j) / 4096 := by omega
  have hg_hi : (53311 + 3 * k + j) / 4096 ≤ 14 := by omega
  generalize hgv : (53311 + 3 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_13 (53311 + 3 * k + j) (by omega) (by omega)]
    rw [l1Call_bnd4096_13 (53311 + 3 * k + j - 53248) (by omega) (by omega)]
    exact congrArg l1CallWord (by omega)
  · rw [get_commitCode_to_commitCode_1_14 (53311 + 3 * k + j) (by omega) (by omega)]
    rw [l1Call_bnd4096_14 (53311 + 3 * k + j - 57344) (by omega) (by omega)]
    exact congrArg l1CallWord (by omega)

def l2PairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x06050513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | _ => 0#32

def l2PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (96#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_l2PairWord (j : Fin 6) :
    decodeInstruction (l2PairWord j.val) = some (l2PairInstr j.val) := by
  revert j; decide

private abbrev l2Pair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755

private theorem l2Pair_chunk64_p0 (r : Fin 64) :
    l2Pair_c64_p0.get 32 r = l2PairWord ((r.val + 0) % 6) := by
  revert r; decide

private abbrev l2Pair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883

private theorem l2Pair_chunk64_p2 (r : Fin 64) :
    l2Pair_c64_p2.get 32 r = l2PairWord ((r.val + 2) % 6) := by
  revert r; decide

private abbrev l2Pair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483

private theorem l2Pair_chunk64_p4 (r : Fin 64) :
    l2Pair_c64_p4.get 32 r = l2PairWord ((r.val + 4) % 6) := by
  revert r; decide

private theorem l2Pair_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_115.get 32 ⟨r, hr⟩ = l2PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 64) l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 r hr
  have hdef : MoonArtifact.commitCode_0_115 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p0 l2Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p2 l2Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p4 l2Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p0 l2Pair_c64_p4))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_1, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_2, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_3, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_4, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_5, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_6, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_7, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)

private theorem l2Pair_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_113.get 32 ⟨r, hr⟩ = l2PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 64) l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_113 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p2 l2Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p4 l2Pair_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p0 l2Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p2 l2Pair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_1, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_2, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_3, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_4, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_5, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_6, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_7, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)

private theorem l2Pair_blk512_p4 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_114.get 32 ⟨r, hr⟩ = l2PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 64) l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_114 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p4 l2Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p0 l2Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p2 l2Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p4 l2Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_1, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_2, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_3, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_4, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_5, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_6, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_7, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)

private theorem l2Pair_bnd64_897 (i : Fin 38) :
    (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594266352274101783360133553644653483110803992673741747102673841019853610558311441410181084848534288286881814970678290331215513809800344636504997953242083782004841426844555785362903381692548683945986296097963597099587446619911923279654505026589699683075).get 32 ⟨26 + i.val, by omega⟩ =
      l2PairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem l2Pair_bnd512_112 (r : Nat) (hlo : 90 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_112.get 32 ⟨r, by omega⟩ = l2PairWord ((57344 + r - 57434) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 16166270485363883128481367809098153567797458605518823055942671321195417409159725743215744868980478007586138399771646148353309132225517278640932567746397337773301315539303028118758730444343952612688803848935310611045776696018755853430380898945794348940057753364192292728522469252618756195459722410082090319648954073741066464054268563158851343383798244592821740742531988677869507632769906116148694314245664041451808176814620475398637138294706648499962312642467115222984034622729361865024015863362169659178998086383126234181762610107595617927850356623038951010686591312640318256326197045244061238656757806512002218460691) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594266352274101783360133553644653483110803992673741747102673841019853610558311441410181084848534288286881814970678290331215513809800344636504997953242083782004841426844555785362903381692548683945986296097963597099587446619911923279654505026589699683075) l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 l2Pair_c64_p2 l2Pair_c64_p0 l2Pair_c64_p4 r (by omega)
  have hdef : MoonArtifact.commitCode_0_112 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 16166270485363883128481367809098153567797458605518823055942671321195417409159725743215744868980478007586138399771646148353309132225517278640932567746397337773301315539303028118758730444343952612688803848935310611045776696018755853430380898945794348940057753364192292728522469252618756195459722410082090319648954073741066464054268563158851343383798244592821740742531988677869507632769906116148694314245664041451808176814620475398637138294706648499962312642467115222984034622729361865024015863362169659178998086383126234181762610107595617927850356623038951010686591312640318256326197045244061238656757806512002218460691) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594266352274101783360133553644653483110803992673741747102673841019853610558311441410181084848534288286881814970678290331215513809800344636504997953242083782004841426844555785362903381692548683945986296097963597099587446619911923279654505026589699683075)) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p2 l2Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p4 l2Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l2Pair_c64_p0 l2Pair_c64_p4))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · rw [pick8_1]; have h := l2Pair_bnd64_897 ⟨r % 64 - 26, by omega⟩
    dsimp only at h
    have heq1 : 26 + (r % 64 - 26) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 26)) % 6 = (57344 + r - 57434) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_2, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_3, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_4, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_5, l2Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_6, l2Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)
  · rw [pick8_7, l2Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l2PairWord (by dsimp only; omega)

private theorem l2Pair_bnd64_928 (i : Fin 40) :
    (ArtifactEncoding.Packed.chunk 64 8084700642970528894271169131613921478919074874843753469109440410883750966883703669465209707059399169203688447118446796099265087640036994580387618629275339521319064482981451893923783335521517109501439305957828477808483257407203733451633974581431824435596012319636151773375973170148443243780375841951870712878103674447533734013323985140597436563459387726488101853517173742768917616765379383569993183384321858816830263296609432814824279683191084484634504892577059314660297747684850820983632990589347754022367153673099238599691970214011365258296520349477568501381928214051255492598432217576514755615214409674620644884595).get 32 ⟨0 + i.val, by omega⟩ =
      l2PairWord ((1958 + i.val) % 6) := by
  revert i; decide

private theorem l2Pair_bnd512_116 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 40) :
    MoonArtifact.commitCode_0_116.get 32 ⟨r, by omega⟩ = l2PairWord ((59392 + r - 57434) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 8084700642970528894271169131613921478919074874843753469109440410883750966883703669465209707059399169203688447118446796099265087640036994580387618629275339521319064482981451893923783335521517109501439305957828477808483257407203733451633974581431824435596012319636151773375973170148443243780375841951870712878103674447533734013323985140597436563459387726488101853517173742768917616765379383569993183384321858816830263296609432814824279683191084484634504892577059314660297747684850820983632990589347754022367153673099238599691970214011365258296520349477568501381928214051255492598432217576514755615214409674620644884595) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961634341254905471380966515261086307091) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) r (by omega)
  have hdef : MoonArtifact.commitCode_0_116 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 8084700642970528894271169131613921478919074874843753469109440410883750966883703669465209707059399169203688447118446796099265087640036994580387618629275339521319064482981451893923783335521517109501439305957828477808483257407203733451633974581431824435596012319636151773375973170148443243780375841951870712878103674447533734013323985140597436563459387726488101853517173742768917616765379383569993183384321858816830263296609432814824279683191084484634504892577059314660297747684850820983632990589347754022367153673099238599691970214011365258296520349477568501381928214051255492598432217576514755615214409674620644884595) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961634341254905471380966515261086307091)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := l2Pair_bnd64_928 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (1958 + (r % 64 - 0)) % 6 = (59392 + r - 57434) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem l2Pair_bnd4096_14 (r : Nat) (hlo : 90 ≤ r) (hhi : r < 2088) :
    MoonArtifact.commitCode_1_14.get 32 ⟨r, by omega⟩ = l2PairWord ((57344 + r - 57434) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 r (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l2Pair_bnd512_112 (r % 512) (by omega) (by omega)]
    exact congrArg l2PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_113 = MoonArtifact.commitCode_0_113 := rfl
    rw [hblk, l2Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l2PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_114 = MoonArtifact.commitCode_0_114 := rfl
    rw [hblk, l2Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l2PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_115 = MoonArtifact.commitCode_0_115 := rfl
    rw [hblk, l2Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l2PairWord (by omega)
  · rw [pick8_4, l2Pair_bnd512_116 (r % 512) (by omega) (by omega)]
    exact congrArg l2PairWord (by omega)
  · omega
  · omega
  · omega

theorem commit_fetch_l2_bulk (state : MachineState) (k j : Nat) (hk : k < 333) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (l2PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (57434 + 6 * k + j) (by omega)
    (l2PairWord j) hpc _ (l2PairInstr j) (decode_l2PairWord ⟨j, hj⟩)
  have hg_lo : 14 ≤ (57434 + 6 * k + j) / 4096 := by omega
  have hg_hi : (57434 + 6 * k + j) / 4096 ≤ 14 := by omega
  generalize hgv : (57434 + 6 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_14 (57434 + 6 * k + j) (by omega) (by omega)]
    rw [l2Pair_bnd4096_14 (57434 + 6 * k + j - 57344) (by omega) (by omega)]
    exact congrArg l2PairWord (by omega)

def binUPairWord : Nat → BitVec 32
  | 0 => 0x06050513#32
  | 1 => 0x04060613#32
  | 2 => 0x00000073#32
  | 3 => 0x06050513#32
  | 4 => 0x02060613#32
  | 5 => 0x00000073#32
  | _ => 0#32

def binUPairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (96#12))
  | 1 => .base (.ADDI .x12 .x12 (64#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (96#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

theorem decode_binUPairWord (j : Fin 6) :
    decodeInstruction (binUPairWord j.val) = some (binUPairInstr j.val) := by
  revert j; decide

private abbrev binUPair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755

private theorem binUPair_chunk64_p0 (r : Fin 64) :
    binUPair_c64_p0.get 32 r = binUPairWord ((r.val + 0) % 6) := by
  revert r; decide

private abbrev binUPair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883

private theorem binUPair_chunk64_p2 (r : Fin 64) :
    binUPair_c64_p2.get 32 r = binUPairWord ((r.val + 2) % 6) := by
  revert r; decide

private abbrev binUPair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483

private theorem binUPair_chunk64_p4 (r : Fin 64) :
    binUPair_c64_p4.get 32 r = binUPairWord ((r.val + 4) % 6) := by
  revert r; decide

private theorem binUPair_bnd64_929 (i : Fin 60) :
    (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961634341254905471380966515261086307091).get 32 ⟨4 + i.val, by omega⟩ =
      binUPairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem binUPair_bnd512_116 (r : Nat) (hlo : 68 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_116.get 32 ⟨r, by omega⟩ = binUPairWord ((59392 + r - 59460) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 8084700642970528894271169131613921478919074874843753469109440410883750966883703669465209707059399169203688447118446796099265087640036994580387618629275339521319064482981451893923783335521517109501439305957828477808483257407203733451633974581431824435596012319636151773375973170148443243780375841951870712878103674447533734013323985140597436563459387726488101853517173742768917616765379383569993183384321858816830263296609432814824279683191084484634504892577059314660297747684850820983632990589347754022367153673099238599691970214011365258296520349477568501381928214051255492598432217576514755615214409674620644884595) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961634341254905471380966515261086307091) binUPair_c64_p0 binUPair_c64_p4 binUPair_c64_p2 binUPair_c64_p0 binUPair_c64_p4 binUPair_c64_p2 r (by omega)
  have hdef : MoonArtifact.commitCode_0_116 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 8084700642970528894271169131613921478919074874843753469109440410883750966883703669465209707059399169203688447118446796099265087640036994580387618629275339521319064482981451893923783335521517109501439305957828477808483257407203733451633974581431824435596012319636151773375973170148443243780375841951870712878103674447533734013323985140597436563459387726488101853517173742768917616765379383569993183384321858816830263296609432814824279683191084484634504892577059314660297747684850820983632990589347754022367153673099238599691970214011365258296520349477568501381928214051255492598432217576514755615214409674620644884595) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961634341254905471380966515261086307091)) (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p0 binUPair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p2 binUPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p4 binUPair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · rw [pick8_1]; have h := binUPair_bnd64_929 ⟨r % 64 - 4, by omega⟩
    dsimp only at h
    have heq1 : 4 + (r % 64 - 4) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 4)) % 6 = (59392 + r - 59460) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_2, binUPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_3, binUPair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_4, binUPair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_5, binUPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_6, binUPair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_7, binUPair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)

private theorem binUPair_bnd64_941 (i : Fin 4) :
    (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003).get 32 ⟨0 + i.val, by omega⟩ =
      binUPairWord ((764 + i.val) % 6) := by
  revert i; decide

private theorem binUPair_bnd512_117 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 324) :
    MoonArtifact.commitCode_0_117.get 32 ⟨r, by omega⟩ = binUPairWord ((59904 + r - 59460) % 6) := by
  have h8 := packed_get_join8 (S := 64) binUPair_c64_p0 binUPair_c64_p4 binUPair_c64_p2 binUPair_c64_p0 binUPair_c64_p4 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) r (by omega)
  have hdef : MoonArtifact.commitCode_0_117 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p0 binUPair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p2 binUPair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binUPair_c64_p4 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, binUPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_1, binUPair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_2, binUPair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_3, binUPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_4, binUPair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg binUPairWord (by dsimp only; omega)
  · rw [pick8_5]; have h := binUPair_bnd64_941 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (764 + (r % 64 - 0)) % 6 = (59904 + r - 59460) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega

private theorem binUPair_bnd4096_14 (r : Nat) (hlo : 2116 ≤ r) (hhi : r < 2884) :
    MoonArtifact.commitCode_1_14.get 32 ⟨r, by omega⟩ = binUPairWord ((57344 + r - 59460) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 r (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · omega
  · omega
  · rw [pick8_4, binUPair_bnd512_116 (r % 512) (by omega) (by omega)]
    exact congrArg binUPairWord (by omega)
  · rw [pick8_5, binUPair_bnd512_117 (r % 512) (by omega) (by omega)]
    exact congrArg binUPairWord (by omega)
  · omega
  · omega

theorem commit_fetch_binu_bulk (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (59460 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (binUPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (59460 + 6 * k + j) (by omega)
    (binUPairWord j) hpc _ (binUPairInstr j) (decode_binUPairWord ⟨j, hj⟩)
  have hg_lo : 14 ≤ (59460 + 6 * k + j) / 4096 := by omega
  have hg_hi : (59460 + 6 * k + j) / 4096 ≤ 14 := by omega
  generalize hgv : (59460 + 6 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_14 (59460 + 6 * k + j) (by omega) (by omega)]
    rw [binUPair_bnd4096_14 (59460 + 6 * k + j - 57344) (by omega) (by omega)]
    exact congrArg binUPairWord (by omega)

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

private abbrev binPair_c64_p7 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531

private theorem binPair_chunk64_p7 (r : Fin 64) :
    binPair_c64_p7.get 32 r = binPairWord ((r.val + 7) % 8) := by
  revert r; decide

private theorem binPair_bnd64_941 (i : Fin 31) :
    (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003).get 32 ⟨33 + i.val, by omega⟩ =
      binPairWord ((0 + i.val) % 8) := by
  revert i; decide

private theorem binPair_bnd512_117 (r : Nat) (hlo : 353 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_117.get 32 ⟨r, by omega⟩ = binPairWord ((59904 + r - 60257) % 8) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003) binPair_c64_p7 binPair_c64_p7 r (by omega)
  have hdef : MoonArtifact.commitCode_0_117 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307375215195224401616811721300482765055848768080121259124340863122690369007955941117127847663589825436672685203515006720451252794605246503052884730283669773336132719964802908066084389243555795487248731150571893007722735360666796199648318916036074707996753434903485243150990227191649190467905154016815052685747180313510003)) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p7 binPair_c64_p7))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [pick8_5]; have h := binPair_bnd64_941 ⟨r % 64 - 33, by omega⟩
    dsimp only at h
    have heq1 : 33 + (r % 64 - 33) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 33)) % 8 = (59904 + r - 60257) % 8 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_6, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_7, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)

private theorem binPair_bnd64_949 (i : Fin 33) :
    (ArtifactEncoding.Packed.chunk 64 257658950384598601347187468948470213667526904081302411761859711806817698632339880458817910949571290459493528592585612747271604237978248456961809668513452051279559166371195194976804767859086202524083232127659218209598552409410181469908104105652283221935279859750562936755510153957223201685012908943985319365049338984190842443932457761932481224973157088067402869260759675847665305663823136323218346812694020938695027636702382127019304325676379309658743355563075299145858936788100150308845723635874161003400540497640967062854100876895075892116768160025864226165551090291804217237270701332517138870506763486448583057187).get 32 ⟨0 + i.val, by omega⟩ =
      binPairWord ((479 + i.val) % 8) := by
  revert i; decide

private theorem binPair_bnd512_118 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 353) :
    MoonArtifact.commitCode_0_118.get 32 ⟨r, by omega⟩ = binPairWord ((60416 + r - 60257) % 8) := by
  have h8 := packed_get_join8 (S := 64) binPair_c64_p7 binPair_c64_p7 binPair_c64_p7 binPair_c64_p7 binPair_c64_p7 (ArtifactEncoding.Packed.chunk 64 257658950384598601347187468948470213667526904081302411761859711806817698632339880458817910949571290459493528592585612747271604237978248456961809668513452051279559166371195194976804767859086202524083232127659218209598552409410181469908104105652283221935279859750562936755510153957223201685012908943985319365049338984190842443932457761932481224973157088067402869260759675847665305663823136323218346812694020938695027636702382127019304325676379309658743355563075299145858936788100150308845723635874161003400540497640967062854100876895075892116768160025864226165551090291804217237270701332517138870506763486448583057187) (ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497195964954505848121274941722672085850348977029878249466040334696670868375275600606513041985083189452303727812509043408700928929251438139326506345083314769807415427881663718499853055146757608890183060214877781751473473837838553385700699537045542653531469393643111265027) (ArtifactEncoding.Packed.chunk 64 192414428721919423878806667985218002162932095286161679050933121754777833203943473800090820478160835380138638469928459857791784808935910990701206151482474913349969224815372215337639535127595439581195364598825324447551080937736210908322549822471158032466523741492527007298052626645311405722645004964394575160813560478188176311243673000331939002676144148063187243166832015410591169274247713763860271075718169914825386642941452469352690296401982127866681021419336416999297413768007673685340754576170790505963569508070223014254454531915871504277586610438815950139208752893778401527792438798135154113771664625409689191699) r (by omega)
  have hdef : MoonArtifact.commitCode_0_118 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p7 binPair_c64_p7) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p7 binPair_c64_p7)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p7 (ArtifactEncoding.Packed.chunk 64 257658950384598601347187468948470213667526904081302411761859711806817698632339880458817910949571290459493528592585612747271604237978248456961809668513452051279559166371195194976804767859086202524083232127659218209598552409410181469908104105652283221935279859750562936755510153957223201685012908943985319365049338984190842443932457761932481224973157088067402869260759675847665305663823136323218346812694020938695027636702382127019304325676379309658743355563075299145858936788100150308845723635874161003400540497640967062854100876895075892116768160025864226165551090291804217237270701332517138870506763486448583057187)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497195964954505848121274941722672085850348977029878249466040334696670868375275600606513041985083189452303727812509043408700928929251438139326506345083314769807415427881663718499853055146757608890183060214877781751473473837838553385700699537045542653531469393643111265027) (ArtifactEncoding.Packed.chunk 64 192414428721919423878806667985218002162932095286161679050933121754777833203943473800090820478160835380138638469928459857791784808935910990701206151482474913349969224815372215337639535127595439581195364598825324447551080937736210908322549822471158032466523741492527007298052626645311405722645004964394575160813560478188176311243673000331939002676144148063187243166832015410591169274247713763860271075718169914825386642941452469352690296401982127866681021419336416999297413768007673685340754576170790505963569508070223014254454531915871504277586610438815950139208752893778401527792438798135154113771664625409689191699)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_1, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_2, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_3, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_4, binPair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_5]; have h := binPair_bnd64_949 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (479 + (r % 64 - 0)) % 8 = (60416 + r - 60257) % 8 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega

private theorem binPair_bnd4096_14 (r : Nat) (hlo : 2913 ≤ r) (hhi : r < 3425) :
    MoonArtifact.commitCode_1_14.get 32 ⟨r, by omega⟩ = binPairWord ((57344 + r - 60257) % 8) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 r (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [pick8_5, binPair_bnd512_117 (r % 512) (by omega) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_6, binPair_bnd512_118 (r % 512) (by omega) (by omega)]
    exact congrArg binPairWord (by omega)
  · omega

theorem commit_fetch_bin_bulk (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (60257 + 8 * k + j))) :
    fetch (submission.image .commit) state = some (binPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (60257 + 8 * k + j) (by omega)
    (binPairWord j) hpc _ (binPairInstr j) (decode_binPairWord ⟨j, hj⟩)
  have hg_lo : 14 ≤ (60257 + 8 * k + j) / 4096 := by omega
  have hg_hi : (60257 + 8 * k + j) / 4096 ≤ 14 := by omega
  generalize hgv : (60257 + 8 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_14 (60257 + 8 * k + j) (by omega) (by omega)]
    rw [binPair_bnd4096_14 (60257 + 8 * k + j - 57344) (by omega) (by omega)]
    exact congrArg binPairWord (by omega)

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

private abbrev bin238Pair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 192414428721919423878806667985218002162932095286161679050933121754777833203943473800090820478160835380138638469928459857791784808935910990701206151482474913349969224815372215337639535127595439581195364598825324447551080937736210908322549822471158032466523741492527007298052626645311405722645004964394575160813560478188176311243673000331939002676144148063187243166832015410591169274247713763860271075718169914825386642941452469352690296401982127866681021419336416999297413768007673685340754576170790505963569508070223014254454531915871504277586610438815950139208752893778401527792438798135154113771664625409689191699

private theorem bin238Pair_chunk64_p0 (r : Fin 64) :
    bin238Pair_c64_p0.get 32 r = bin238PairWord ((r.val + 0) % 12) := by
  revert r; decide

private abbrev bin238Pair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020807088133615940332702626983286515005783439185479853961055163054691736655223201614834975692151174104146452007384576870020287680630016861245868579188083761477395907274000834836819015621074656622506108127360523770336787097286904049227385894600672411977888516281922833275870922174672440313909185118325630210996464588003425074730327114809420253443197464389741183412454975553511708278634017273673819949023580856045464686488010056384591083978622604386650772537552973068276816825781891678124423028415125686188301028093194564570917363868607664422964599056997713819032636169572275764898334345032178352289073046188851

private theorem bin238Pair_chunk64_p4 (r : Fin 64) :
    bin238Pair_c64_p4.get 32 r = bin238PairWord ((r.val + 4) % 12) := by
  revert r; decide

private abbrev bin238Pair_c64_p8 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497205614306667439191596978559845098719236811094293416755528640600287790605233036320564790186207877619559094161591578729729596742227980096627405882643970175404758776702182329322617011523379931299520395637276628413381059327390925302148929837591563806943549026427776008307

private theorem bin238Pair_chunk64_p8 (r : Fin 64) :
    bin238Pair_c64_p8.get 32 r = bin238PairWord ((r.val + 8) % 12) := by
  revert r; decide

private theorem bin238Pair_blk512_p4 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_119.get 32 ⟨r, hr⟩ = bin238PairWord ((r + 4) % 12) := by
  have h8 := packed_get_join8 (S := 64) bin238Pair_c64_p4 bin238Pair_c64_p8 bin238Pair_c64_p0 bin238Pair_c64_p4 bin238Pair_c64_p8 bin238Pair_c64_p0 bin238Pair_c64_p4 bin238Pair_c64_p8 r hr
  have hdef : MoonArtifact.commitCode_0_119 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p4 bin238Pair_c64_p8) (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p0 bin238Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p8 bin238Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p4 bin238Pair_c64_p8))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, bin238Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_1, bin238Pair_chunk64_p8 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_2, bin238Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_3, bin238Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_4, bin238Pair_chunk64_p8 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_5, bin238Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_6, bin238Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_7, bin238Pair_chunk64_p8 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)

private theorem bin238Pair_bnd64_950 (i : Fin 36) :
    (ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497195964954505848121274941722672085850348977029878249466040334696670868375275600606513041985083189452303727812509043408700928929251438139326506345083314769807415427881663718499853055146757608890183060214877781751473473837838553385700699537045542653531469393643111265027).get 32 ⟨28 + i.val, by omega⟩ =
      bin238PairWord ((0 + i.val) % 12) := by
  revert i; decide

private theorem bin238Pair_bnd512_118 (r : Nat) (hlo : 412 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_118.get 32 ⟨r, by omega⟩ = bin238PairWord ((60416 + r - 60828) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 257658950384598601347187468948470213667526904081302411761859711806817698632339880458817910949571290459493528592585612747271604237978248456961809668513452051279559166371195194976804767859086202524083232127659218209598552409410181469908104105652283221935279859750562936755510153957223201685012908943985319365049338984190842443932457761932481224973157088067402869260759675847665305663823136323218346812694020938695027636702382127019304325676379309658743355563075299145858936788100150308845723635874161003400540497640967062854100876895075892116768160025864226165551090291804217237270701332517138870506763486448583057187) (ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497195964954505848121274941722672085850348977029878249466040334696670868375275600606513041985083189452303727812509043408700928929251438139326506345083314769807415427881663718499853055146757608890183060214877781751473473837838553385700699537045542653531469393643111265027) bin238Pair_c64_p0 r (by omega)
  have hdef : MoonArtifact.commitCode_0_118 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221210663538806799201097435099966560354465780520437385701413819997512415814768404678155331259547002855734503037412962168429471625416997986757768646769937256855815249176123510708227392503692644566228388984165327592403825580550861157766405585755017702710810294146163543307374096952433858348664815052347681511285869990993131640251399555239785621641257816500304065095462682358936978048216597741131725872978755686594234577878076932212589778895876101181739699664627944566616447739850827242103317511750083132428503839761148513581191717963866640072383985925959340039466171651705045444075238858531) (ArtifactEncoding.Packed.chunk 64 257658950384598601347187468948470213667526904081302411761859711806817698632339880458817910949571290459493528592585612747271604237978248456961809668513452051279559166371195194976804767859086202524083232127659218209598552409410181469908104105652283221935279859750562936755510153957223201685012908943985319365049338984190842443932457761932481224973157088067402869260759675847665305663823136323218346812694020938695027636702382127019304325676379309658743355563075299145858936788100150308845723635874161003400540497640967062854100876895075892116768160025864226165551090291804217237270701332517138870506763486448583057187)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212893002569946798269015129332002794555695599206375719412602163618787441952748414891119418482704112219530178063080082657703511710236625830768266928145871616363681435475207476026231634645840361473946051047614898713862937301315018517133201224286616684890006625546474431198430602401101820412850616468844903947159344497195964954505848121274941722672085850348977029878249466040334696670868375275600606513041985083189452303727812509043408700928929251438139326506345083314769807415427881663718499853055146757608890183060214877781751473473837838553385700699537045542653531469393643111265027) bin238Pair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [pick8_6]; have h := bin238Pair_bnd64_950 ⟨r % 64 - 28, by omega⟩
    dsimp only at h
    have heq1 : 28 + (r % 64 - 28) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 28)) % 12 = (60416 + r - 60828) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_7, bin238Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)

private theorem bin238Pair_bnd4096_14 (r : Nat) (hlo : 3484 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_14.get 32 ⟨r, by omega⟩ = bin238PairWord ((57344 + r - 60828) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 r (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [pick8_6, bin238Pair_bnd512_118 (r % 512) (by omega) (by omega)]
    exact congrArg bin238PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_119 = MoonArtifact.commitCode_0_119 := rfl
    rw [hblk, bin238Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg bin238PairWord (by omega)

private theorem get_commitCode_1_15_to_commitCode_0_120 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 227) :
    MoonArtifact.commitCode_1_15.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_120.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode_1_15
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_120 (idx : Nat) (hlo : 61440 ≤ idx) (hhi : idx < 61667) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_120.get 32 ⟨idx - 61440, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_15 idx (by omega) (by omega)]
  rw [get_commitCode_1_15_to_commitCode_0_120 (idx - 61440) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem bin238Pair_bnd64_962 (i : Fin 28) :
    (ArtifactEncoding.Packed.chunk 64 315596597692883776020656149388887626568698942543104289586472212823601780262077897691228501588746480311086888156131513424446373455088984327447138213082853767775194521354071276317546564691922453982267963783722318104199962417538032870499908119717476601377008438207674680197548625822889820326864781530821781144547367500041577662428660873495750527330534004450181567063186265766932076592676061259063281977866427882948008221252886707168079451401832787380184632607431167029071928291557306682413899046741084948213847510118864359410407801642073544324968958652186659306589556241091215819776237197413504966810789100051096404083).get 32 ⟨0 + i.val, by omega⟩ =
      bin238PairWord ((740 + i.val) % 12) := by
  revert i; decide

private theorem bin238Pair_bnd512_120 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 156) :
    MoonArtifact.commitCode_0_120.get 32 ⟨r, by omega⟩ = bin238PairWord ((61440 + r - 60828) % 12) := by
  have hq : r / 64 < 4 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_120
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p0 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 0) % 12 = (61440 + r - 60828) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_120
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p4 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 4) % 12 = (61440 + r - 60828) % 12 := by omega
    rw [← heq2, ← h]
  · unfold MoonArtifact.commitCode_0_120
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_bnd64_962 ⟨r - 128 - 0, by omega⟩
    dsimp only at h
    have heq2 : (740 + (r - 128 - 0)) % 12 = (61440 + r - 60828) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · omega

theorem commit_fetch_bin238_bulk (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (60828 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (bin238PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (60828 + 12 * k + j) (by omega)
    (bin238PairWord j) hpc _ (bin238PairInstr j) (decode_bin238PairWord ⟨j, hj⟩)
  by_cases hfull : 60828 + 12 * k + j < 61440
  ·
    have hg_lo : 14 ≤ (60828 + 12 * k + j) / 4096 := by omega
    have hg_hi : (60828 + 12 * k + j) / 4096 ≤ 14 := by omega
    generalize hgv : (60828 + 12 * k + j) / 4096 = g at hg_lo hg_hi ⊢
    interval_cases g
    · rw [get_commitCode_to_commitCode_1_14 (60828 + 12 * k + j) (by omega) (by omega)]
      rw [bin238Pair_bnd4096_14 (60828 + 12 * k + j - 57344) (by omega) (by omega)]
      exact congrArg bin238PairWord (by omega)
  ·
    have hb_lo : 120 ≤ (60828 + 12 * k + j) / 512 := by omega
    have hb_hi : (60828 + 12 * k + j) / 512 ≤ 120 := by omega
    generalize hbv : (60828 + 12 * k + j) / 512 = b at hb_lo hb_hi ⊢
    interval_cases b
    · rw [get_commitCode_to_commitCode_0_120 (60828 + 12 * k + j) (by omega) (by omega)]
      rw [bin238Pair_bnd512_120 (60828 + 12 * k + j - 61440) (by omega) (by omega)]
      exact congrArg bin238PairWord (by omega)

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (213#12))
  | 4 => .base (.SLLI .x6 .x6 (11#6))
  | 5 => .base (.ADDI .x6 .x6 (683#12))
  | 6 => .base (.SLLI .x6 .x6 (11#6))
  | 7 => .base (.ADDI .x6 .x6 (224#12))
  | 8 => .base (.ADD .x18 .x9 .x6)
  | 9 => .base (.ADDI .x5 .x0 (2#12))
  | 10 => .base (.ADDI .x10 .x18 (72#12))
  | 11 => .base (.ADDI .x11 .x0 (40#12))
  | 12 => .base (.ADDI .x6 .x0 (368#12))
  | 13 => .base (.SLLI .x6 .x6 (11#6))
  | 14 => .base (.SLLI .x6 .x6 (11#6))
  | 15 => .base (.ADDI .x6 .x6 (72#12))
  | 16 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 512) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_0.get 32 ⟨idx - 0, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitPrefixInstr_b0 (i : Fin 17) :
    decodeInstruction (MoonArtifact.commitCode_0_0.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 17)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_0 idx (by omega) (by omega)]
  have h := decode_commitPrefixInstr_b0 ⟨idx - 0, by omega⟩
  dsimp only at h
  have heq1 : 0 + (idx - 0) = idx - 0 := by omega
  have heq2 : 0 + (idx - 0) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid0Instr : Nat → Instruction
  | 4113 => .base (.BEQ .x10 .x19 (8#13))
  | 4114 => .base (.JAL .x0 (2080764#21))
  | 4115 => .base (.ADDI .x5 .x0 (0#12))
  | 4116 => .base (.ADDI .x11 .x0 (96#12))
  | 4117 => .base (.ADDI .x13 .x0 (0#12))
  | 4118 => .base (.ADDI .x10 .x8 (3840#12))
  | 4119 => .base (.ADDI .x6 .x0 (1023#12))
  | 4120 => .base (.SLLI .x6 .x6 (11#6))
  | 4121 => .base (.ADDI .x6 .x6 (2047#12))
  | 4122 => .base (.SLLI .x6 .x6 (11#6))
  | 4123 => .base (.ADDI .x6 .x6 (1792#12))
  | 4124 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_8 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 4608) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_8.get 32 ⟨idx - 4096, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid0Instr_b8 (i : Fin 12) :
    decodeInstruction (MoonArtifact.commitCode_0_8.get 32 ⟨17 + i.val, by omega⟩) =
      some (commitMid0Instr (4113 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 4113 ≤ idx) (hhi : idx < 4125)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_8 idx (by omega) (by omega)]
  have h := decode_commitMid0Instr_b8 ⟨idx - 4113, by omega⟩
  dsimp only at h
  have heq1 : 17 + (idx - 4113) = idx - 4096 := by omega
  have heq2 : 4113 + (idx - 4113) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1AInstr : Nat → Instruction
  | 16413 => .base (.BEQ .x10 .x19 (8#13))
  | 16414 => .base (.JAL .x0 (2047996#21))
  | 16415 => .base (.ADDI .x10 .x8 (4000#12))
  | 16416 => .base (.ADDI .x12 .x18 (4064#12))
  | 16417 => .base (.ADDI .x6 .x0 (1023#12))
  | 16418 => .base (.SLLI .x6 .x6 (11#6))
  | 16419 => .base (.ADDI .x6 .x6 (2047#12))
  | 16420 => .base (.SLLI .x6 .x6 (11#6))
  | 16421 => .base (.ADDI .x6 .x6 (1952#12))
  | 16422 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_32 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 16896) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_32.get 32 ⟨idx - 16384, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid1AInstr_b32 (i : Fin 10) :
    decodeInstruction (MoonArtifact.commitCode_0_32.get 32 ⟨29 + i.val, by omega⟩) =
      some (commitMid1AInstr (16413 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 16413 ≤ idx) (hhi : idx < 16423)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_32 idx (by omega) (by omega)]
  have h := decode_commitMid1AInstr_b32 ⟨idx - 16413, by omega⟩
  dsimp only at h
  have heq1 : 29 + (idx - 16413) = idx - 16384 := by omega
  have heq2 : 16413 + (idx - 16413) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1BInstr : Nat → Instruction
  | 40999 => .base (.BEQ .x10 .x19 (8#13))
  | 41000 => .base (.JAL .x0 (1998844#21))
  | 41001 => .base (.ADDI .x10 .x18 (4000#12))
  | 41002 => .base (.ADDI .x12 .x9 (4064#12))
  | 41003 => .base (.ADDI .x6 .x0 (367#12))
  | 41004 => .base (.SLLI .x6 .x6 (11#6))
  | 41005 => .base (.ADDI .x6 .x6 (2047#12))
  | 41006 => .base (.SLLI .x6 .x6 (11#6))
  | 41007 => .base (.ADDI .x6 .x6 (1952#12))
  | 41008 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_80 (idx : Nat) (hlo : 40960 ≤ idx) (hhi : idx < 41472) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_80.get 32 ⟨idx - 40960, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87 (idx - 40960) (by omega)
  have hdef : MoonArtifact.commitCode_1_10 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 40960) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid1BInstr_b80 (i : Fin 10) :
    decodeInstruction (MoonArtifact.commitCode_0_80.get 32 ⟨39 + i.val, by omega⟩) =
      some (commitMid1BInstr (40999 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 40999 ≤ idx) (hhi : idx < 41009)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_80 idx (by omega) (by omega)]
  have h := decode_commitMid1BInstr_b80 ⟨idx - 40999, by omega⟩
  dsimp only at h
  have heq1 : 39 + (idx - 40999) = idx - 40960 := by omega
  have heq2 : 40999 + (idx - 40999) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1CInstr : Nat → Instruction
  | 53297 => .base (.BEQ .x10 .x19 (8#13))
  | 53298 => .base (.JAL .x0 (2047996#21))
  | 53299 => .base (.ADDI .x10 .x9 (4000#12))
  | 53300 => .base (.ADDI .x6 .x0 (128#12))
  | 53301 => .base (.SLLI .x6 .x6 (11#6))
  | 53302 => .base (.SLLI .x6 .x6 (11#6))
  | 53303 => .base (.ADD .x12 .x9 .x6)
  | 53304 => .base (.ADDI .x12 .x12 (4064#12))
  | 53305 => .base (.ADDI .x6 .x0 (127#12))
  | 53306 => .base (.SLLI .x6 .x6 (11#6))
  | 53307 => .base (.ADDI .x6 .x6 (2047#12))
  | 53308 => .base (.SLLI .x6 .x6 (11#6))
  | 53309 => .base (.ADDI .x6 .x6 (1920#12))
  | 53310 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_104 (idx : Nat) (hlo : 53248 ≤ idx) (hhi : idx < 53760) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_104.get 32 ⟨idx - 53248, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_13 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111 (idx - 53248) (by omega)
  have hdef : MoonArtifact.commitCode_1_13 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 53248) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid1CInstr_b104 (i : Fin 14) :
    decodeInstruction (MoonArtifact.commitCode_0_104.get 32 ⟨49 + i.val, by omega⟩) =
      some (commitMid1CInstr (53297 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (hlo : 53297 ≤ idx) (hhi : idx < 53311)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_104 idx (by omega) (by omega)]
  have h := decode_commitMid1CInstr_b104 ⟨idx - 53297, by omega⟩
  dsimp only at h
  have heq1 : 49 + (idx - 53297) = idx - 53248 := by omega
  have heq2 : 53297 + (idx - 53297) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid2AInstr : Nat → Instruction
  | 57406 => .base (.BEQ .x10 .x19 (8#13))
  | 57407 => .base (.JAL .x0 (2080768#21))
  | 57408 => .base (.LD .x6 .x10 (96#12))
  | 57409 => .base (.SD .x12 .x6 (32#12))
  | 57410 => .base (.LD .x6 .x10 (104#12))
  | 57411 => .base (.SD .x12 .x6 (40#12))
  | 57412 => .base (.LD .x6 .x10 (112#12))
  | 57413 => .base (.SD .x12 .x6 (48#12))
  | 57414 => .base (.LD .x6 .x10 (120#12))
  | 57415 => .base (.SD .x12 .x6 (56#12))
  | 57416 => .base (.ADDI .x6 .x0 (128#12))
  | 57417 => .base (.SLLI .x6 .x6 (11#6))
  | 57418 => .base (.SLLI .x6 .x6 (11#6))
  | 57419 => .base (.ADD .x10 .x9 .x6)
  | 57420 => .base (.ADDI .x10 .x10 (4000#12))
  | 57421 => .base (.ADDI .x6 .x0 (170#12))
  | 57422 => .base (.SLLI .x6 .x6 (11#6))
  | 57423 => .base (.ADDI .x6 .x6 (1365#12))
  | 57424 => .base (.SLLI .x6 .x6 (11#6))
  | 57425 => .base (.ADDI .x6 .x6 (704#12))
  | 57426 => .base (.ADD .x12 .x9 .x6)
  | 57427 => .base (.ADDI .x12 .x12 (4032#12))
  | 57428 => .base (.ADDI .x6 .x0 (170#12))
  | 57429 => .base (.SLLI .x6 .x6 (11#6))
  | 57430 => .base (.ADDI .x6 .x6 (1365#12))
  | 57431 => .base (.SLLI .x6 .x6 (11#6))
  | 57432 => .base (.ADDI .x6 .x6 (480#12))
  | 57433 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_112 (idx : Nat) (hlo : 57344 ≤ idx) (hhi : idx < 57856) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_112.get 32 ⟨idx - 57344, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_14 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 (idx - 57344) (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 57344) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid2AInstr_b112 (i : Fin 28) :
    decodeInstruction (MoonArtifact.commitCode_0_112.get 32 ⟨62 + i.val, by omega⟩) =
      some (commitMid2AInstr (57406 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2AInstr (state : MachineState) (idx : Nat) (hlo : 57406 ≤ idx) (hhi : idx < 57434)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2AInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_112 idx (by omega) (by omega)]
  have h := decode_commitMid2AInstr_b112 ⟨idx - 57406, by omega⟩
  dsimp only at h
  have heq1 : 62 + (idx - 57406) = idx - 57344 := by omega
  have heq2 : 57406 + (idx - 57406) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid2BInstr : Nat → Instruction
  | 59432 => .base (.BEQ .x10 .x19 (8#13))
  | 59433 => .base (.JAL .x0 (2089156#21))
  | 59434 => .base (.ADDI .x10 .x10 (96#12))
  | 59435 => .base (.ADDI .x12 .x12 (64#12))
  | 59436 => .base .ECALL
  | 59437 => .base (.LD .x6 .x10 (96#12))
  | 59438 => .base (.SD .x12 .x6 (32#12))
  | 59439 => .base (.LD .x6 .x10 (104#12))
  | 59440 => .base (.SD .x12 .x6 (40#12))
  | 59441 => .base (.LD .x6 .x10 (112#12))
  | 59442 => .base (.SD .x12 .x6 (48#12))
  | 59443 => .base (.LD .x6 .x10 (120#12))
  | 59444 => .base (.SD .x12 .x6 (56#12))
  | 59445 => .base (.ADDI .x24 .x2 (0#12))
  | 59446 => .base (.ADDI .x25 .x2 (64#12))
  | 59447 => .base (.LD .x6 .x24 (0#12))
  | 59448 => .base (.ADD .x10 .x9 .x6)
  | 59449 => .base (.ADDI .x10 .x10 (4000#12))
  | 59450 => .base (.LD .x6 .x24 (8#12))
  | 59451 => .base (.ADD .x12 .x9 .x6)
  | 59452 => .base (.ADDI .x12 .x12 (4032#12))
  | 59453 => .base (.LD .x20 .x24 (16#12))
  | 59454 => .base (.SRLI .x22 .x20 (8#6))
  | 59455 => .base (.BEQ .x22 .x0 (3096#13))
  | 59456 => .base (.SLLI .x6 .x22 (13#6))
  | 59457 => .base (.SLLI .x7 .x22 (14#6))
  | 59458 => .base (.ADD .x6 .x6 .x7)
  | 59459 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_116 (idx : Nat) (hlo : 59392 ≤ idx) (hhi : idx < 59904) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_116.get 32 ⟨idx - 59392, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_14 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 (idx - 57344) (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 57344) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid2BInstr_b116 (i : Fin 28) :
    decodeInstruction (MoonArtifact.commitCode_0_116.get 32 ⟨40 + i.val, by omega⟩) =
      some (commitMid2BInstr (59432 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2BInstr (state : MachineState) (idx : Nat) (hlo : 59432 ≤ idx) (hhi : idx < 59460)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2BInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_116 idx (by omega) (by omega)]
  have h := decode_commitMid2BInstr_b116 ⟨idx - 59432, by omega⟩
  dsimp only at h
  have heq1 : 40 + (idx - 59432) = idx - 59392 := by omega
  have heq2 : 59432 + (idx - 59432) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid3UInstr : Nat → Instruction
  | 60228 => .base (.BNE .x10 .x19 (5120#13))
  | 60229 => .base (.ANDI .x22 .x20 (255#12))
  | 60230 => .base (.SRLI .x22 .x22 (1#6))
  | 60231 => .base (.BEQ .x22 .x0 (36#13))
  | 60232 => .base (.ADDI .x10 .x10 (96#12))
  | 60233 => .base (.ADDI .x12 .x12 (64#12))
  | 60234 => .base .ECALL
  | 60235 => .base (.ADDI .x10 .x10 (96#12))
  | 60236 => .base (.ADDI .x12 .x12 (32#12))
  | 60237 => .base .ECALL
  | 60238 => .base (.ADDI .x22 .x22 (4095#12))
  | 60239 => .base (.BNE .x22 .x0 (8164#13))
  | 60240 => .base (.ADDI .x24 .x24 (32#12))
  | 60241 => .base (.BNE .x24 .x25 (5016#13))
  | 60242 => .base (.ADDI .x25 .x2 (192#12))
  | 60243 => .base (.LD .x6 .x24 (0#12))
  | 60244 => .base (.ADD .x10 .x9 .x6)
  | 60245 => .base (.ADDI .x10 .x10 (4000#12))
  | 60246 => .base (.LD .x6 .x24 (8#12))
  | 60247 => .base (.ADD .x12 .x9 .x6)
  | 60248 => .base (.ADDI .x12 .x12 (4032#12))
  | 60249 => .base (.LD .x20 .x24 (16#12))
  | 60250 => .base (.LD .x21 .x24 (24#12))
  | 60251 => .base (.SRLI .x22 .x20 (7#6))
  | 60252 => .base (.BEQ .x22 .x0 (2072#13))
  | 60253 => .base (.SLLI .x6 .x22 (12#6))
  | 60254 => .base (.SLLI .x7 .x22 (13#6))
  | 60255 => .base (.ADD .x6 .x6 .x7)
  | 60256 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_117 (idx : Nat) (hlo : 59904 ≤ idx) (hhi : idx < 60416) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_117.get 32 ⟨idx - 59904, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_14 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 (idx - 57344) (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 57344) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid3UInstr_b117 (i : Fin 29) :
    decodeInstruction (MoonArtifact.commitCode_0_117.get 32 ⟨324 + i.val, by omega⟩) =
      some (commitMid3UInstr (60228 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid3UInstr (state : MachineState) (idx : Nat) (hlo : 60228 ≤ idx) (hhi : idx < 60257)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid3UInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_117 idx (by omega) (by omega)]
  have h := decode_commitMid3UInstr_b117 ⟨idx - 60228, by omega⟩
  dsimp only at h
  have heq1 : 324 + (idx - 60228) = idx - 59904 := by omega
  have heq2 : 60228 + (idx - 60228) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid3AInstr : Nat → Instruction
  | 60769 => .base (.BNE .x10 .x19 (6144#13))
  | 60770 => .base (.ANDI .x22 .x20 (127#12))
  | 60771 => .base (.SRLI .x22 .x22 (1#6))
  | 60772 => .base (.BEQ .x22 .x0 (44#13))
  | 60773 => .base (.ADDI .x10 .x10 (96#12))
  | 60774 => .base (.ADDI .x12 .x12 (64#12))
  | 60775 => .base .ECALL
  | 60776 => .base (.SH .x12 .x0 (30#12))
  | 60777 => .base (.ADDI .x10 .x10 (96#12))
  | 60778 => .base (.ADDI .x12 .x12 (32#12))
  | 60779 => .base .ECALL
  | 60780 => .base (.SH .x12 .x0 (30#12))
  | 60781 => .base (.ADDI .x22 .x22 (4095#12))
  | 60782 => .base (.BNE .x22 .x0 (8156#13))
  | 60783 => .base (.ANDI .x22 .x20 (1#12))
  | 60784 => .base (.BEQ .x22 .x0 (60#13))
  | 60785 => .base (.ADDI .x10 .x10 (96#12))
  | 60786 => .base (.ADDI .x12 .x12 (64#12))
  | 60787 => .base .ECALL
  | 60788 => .base (.SH .x12 .x0 (30#12))
  | 60789 => .base (.BEQ .x21 .x0 (76#13))
  | 60790 => .base (.LD .x6 .x10 (96#12))
  | 60791 => .base (.SD .x12 .x6 (32#12))
  | 60792 => .base (.LD .x6 .x10 (104#12))
  | 60793 => .base (.SD .x12 .x6 (40#12))
  | 60794 => .base (.LD .x6 .x10 (112#12))
  | 60795 => .base (.SD .x12 .x6 (48#12))
  | 60796 => .base (.LD .x6 .x10 (120#12))
  | 60797 => .base (.SD .x12 .x6 (56#12))
  | 60798 => .base (.JAL .x0 (40#21))
  | 60799 => .base (.BEQ .x21 .x0 (36#13))
  | 60800 => .base (.LD .x6 .x10 (96#12))
  | 60801 => .base (.SD .x12 .x6 (64#12))
  | 60802 => .base (.LD .x6 .x10 (104#12))
  | 60803 => .base (.SD .x12 .x6 (72#12))
  | 60804 => .base (.LD .x6 .x10 (112#12))
  | 60805 => .base (.SD .x12 .x6 (80#12))
  | 60806 => .base (.LD .x6 .x10 (120#12))
  | 60807 => .base (.SD .x12 .x6 (88#12))
  | 60808 => .base (.ADDI .x24 .x24 (32#12))
  | 60809 => .base (.BNE .x24 .x25 (5928#13))
  | 60810 => .base (.ADDI .x25 .x2 (640#12))
  | 60811 => .base (.ADDI .x27 .x0 (1#12))
  | 60812 => .base (.SLLI .x27 .x27 (46#6))
  | 60813 => .base (.ADDI .x27 .x27 (4095#12))
  | 60814 => .base (.LD .x6 .x24 (0#12))
  | 60815 => .base (.ADD .x10 .x9 .x6)
  | 60816 => .base (.ADDI .x10 .x10 (4000#12))
  | 60817 => .base (.LD .x6 .x24 (8#12))
  | 60818 => .base (.ADD .x12 .x9 .x6)
  | 60819 => .base (.ADDI .x12 .x12 (4032#12))
  | 60820 => .base (.LD .x20 .x24 (16#12))
  | 60821 => .base (.LD .x21 .x24 (24#12))
  | 60822 => .base (.SRLI .x22 .x20 (7#6))
  | 60823 => .base (.BEQ .x22 .x0 (3096#13))
  | 60824 => .base (.SLLI .x6 .x22 (12#6))
  | 60825 => .base (.SLLI .x7 .x22 (13#6))
  | 60826 => .base (.ADD .x6 .x6 .x7)
  | 60827 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_118 (idx : Nat) (hlo : 60416 ≤ idx) (hhi : idx < 60928) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_118.get 32 ⟨idx - 60416, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_14 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119 (idx - 57344) (by omega)
  have hdef : MoonArtifact.commitCode_1_14 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_112 MoonArtifact.commitCode_0_113) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_114 MoonArtifact.commitCode_0_115)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_116 MoonArtifact.commitCode_0_117) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_118 MoonArtifact.commitCode_0_119))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 57344) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid3AInstr_b118 (i : Fin 59) :
    decodeInstruction (MoonArtifact.commitCode_0_118.get 32 ⟨353 + i.val, by omega⟩) =
      some (commitMid3AInstr (60769 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid3AInstr (state : MachineState) (idx : Nat) (hlo : 60769 ≤ idx) (hhi : idx < 60828)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid3AInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_118 idx (by omega) (by omega)]
  have h := decode_commitMid3AInstr_b118 ⟨idx - 60769, by omega⟩
  dsimp only at h
  have heq1 : 353 + (idx - 60769) = idx - 60416 := by omega
  have heq2 : 60769 + (idx - 60769) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitTailInstr : Nat → Instruction
  | 61596 => .base (.BNE .x10 .x19 (5120#13))
  | 61597 => .base (.ANDI .x22 .x20 (127#12))
  | 61598 => .base (.SRLI .x22 .x22 (1#6))
  | 61599 => .base (.BEQ .x22 .x0 (60#13))
  | 61600 => .base (.ADDI .x10 .x10 (96#12))
  | 61601 => .base (.ADDI .x12 .x12 (64#12))
  | 61602 => .base .ECALL
  | 61603 => .base (.LD .x6 .x12 (24#12))
  | 61604 => .base (.AND .x6 .x6 .x27)
  | 61605 => .base (.SD .x12 .x6 (24#12))
  | 61606 => .base (.ADDI .x10 .x10 (96#12))
  | 61607 => .base (.ADDI .x12 .x12 (32#12))
  | 61608 => .base .ECALL
  | 61609 => .base (.LD .x6 .x12 (24#12))
  | 61610 => .base (.AND .x6 .x6 .x27)
  | 61611 => .base (.SD .x12 .x6 (24#12))
  | 61612 => .base (.ADDI .x22 .x22 (4095#12))
  | 61613 => .base (.BNE .x22 .x0 (8140#13))
  | 61614 => .base (.ANDI .x22 .x20 (1#12))
  | 61615 => .base (.BEQ .x22 .x0 (68#13))
  | 61616 => .base (.ADDI .x10 .x10 (96#12))
  | 61617 => .base (.ADDI .x12 .x12 (64#12))
  | 61618 => .base .ECALL
  | 61619 => .base (.LD .x6 .x12 (24#12))
  | 61620 => .base (.AND .x6 .x6 .x27)
  | 61621 => .base (.SD .x12 .x6 (24#12))
  | 61622 => .base (.BEQ .x21 .x0 (76#13))
  | 61623 => .base (.LD .x6 .x10 (96#12))
  | 61624 => .base (.SD .x12 .x6 (32#12))
  | 61625 => .base (.LD .x6 .x10 (104#12))
  | 61626 => .base (.SD .x12 .x6 (40#12))
  | 61627 => .base (.LD .x6 .x10 (112#12))
  | 61628 => .base (.SD .x12 .x6 (48#12))
  | 61629 => .base (.LD .x6 .x10 (120#12))
  | 61630 => .base (.SD .x12 .x6 (56#12))
  | 61631 => .base (.JAL .x0 (40#21))
  | 61632 => .base (.BEQ .x21 .x0 (36#13))
  | 61633 => .base (.LD .x6 .x10 (96#12))
  | 61634 => .base (.SD .x12 .x6 (64#12))
  | 61635 => .base (.LD .x6 .x10 (104#12))
  | 61636 => .base (.SD .x12 .x6 (72#12))
  | 61637 => .base (.LD .x6 .x10 (112#12))
  | 61638 => .base (.SD .x12 .x6 (80#12))
  | 61639 => .base (.LD .x6 .x10 (120#12))
  | 61640 => .base (.SD .x12 .x6 (88#12))
  | 61641 => .base (.ADDI .x24 .x24 (32#12))
  | 61642 => .base (.BNE .x24 .x25 (4880#13))
  | 61643 => .base (.ADDI .x6 .x0 (213#12))
  | 61644 => .base (.SLLI .x6 .x6 (11#6))
  | 61645 => .base (.ADDI .x6 .x6 (683#12))
  | 61646 => .base (.SLLI .x6 .x6 (11#6))
  | 61647 => .base (.ADDI .x6 .x6 (96#12))
  | 61648 => .base (.ADD .x10 .x9 .x6)
  | 61649 => .base (.ADDI .x6 .x0 (213#12))
  | 61650 => .base (.SLLI .x6 .x6 (11#6))
  | 61651 => .base (.ADDI .x6 .x6 (683#12))
  | 61652 => .base (.SLLI .x6 .x6 (11#6))
  | 61653 => .base (.ADDI .x6 .x6 (192#12))
  | 61654 => .base (.ADD .x12 .x9 .x6)
  | 61655 => .base .ECALL
  | 61656 => .base (.LD .x6 .x12 (0#12))
  | 61657 => .base (.SD .x26 .x6 (0#12))
  | 61658 => .base (.LD .x6 .x12 (8#12))
  | 61659 => .base (.SD .x26 .x6 (8#12))
  | 61660 => .base (.LD .x6 .x12 (16#12))
  | 61661 => .base (.SD .x26 .x6 (16#12))
  | 61662 => .base (.LD .x6 .x12 (24#12))
  | 61663 => .base (.SD .x26 .x6 (24#12))
  | 61664 => .base (.ADDI .x5 .x0 (1#12))
  | 61665 => .base (.ADDI .x10 .x0 (0#12))
  | 61666 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr_b120 (i : Fin 71) :
    decodeInstruction (MoonArtifact.commitCode_0_120.get 32 ⟨156 + i.val, by omega⟩) =
      some (commitTailInstr (61596 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 61596 ≤ idx) (hhi : idx < 61667)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_120 idx (by omega) (by omega)]
  have h := decode_commitTailInstr_b120 ⟨idx - 61596, by omega⟩
  dsimp only at h
  have heq1 : 156 + (idx - 61596) = idx - 61440 := by omega
  have heq2 : 61596 + (idx - 61596) = idx := by omega
  simp only [heq1, heq2] at h; exact h

/-! ### Opening Program (332 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (792#13))
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
  | 18 => .base (.ADDI .x6 .x0 (213#12))
  | 19 => .base (.SLLI .x6 .x6 (11#6))
  | 20 => .base (.ADDI .x6 .x6 (683#12))
  | 21 => .base (.SLLI .x6 .x6 (11#6))
  | 22 => .base (.ADDI .x6 .x6 (296#12))
  | 23 => .base (.ADD .x18 .x9 .x6)
  | 24 => .base (.ADDI .x19 .x0 (3#12))
  | 25 => .base (.ADDI .x20 .x0 (1#12))
  | 26 => .base (.SLLI .x20 .x20 (11#6))
  | 27 => .base (.ADDI .x20 .x20 (682#12))
  | 28 => .base (.SLLI .x20 .x20 (11#6))
  | 29 => .base (.ADDI .x20 .x20 (1365#12))
  | 30 => .base (.ADDI .x21 .x0 (2#12))
  | 31 => .base (.SLLI .x21 .x21 (11#6))
  | 32 => .base (.LD .x8 .x24 (0#12))
  | 33 => .base (.SRLI .x6 .x8 (1#6))
  | 34 => .base (.SLLI .x7 .x6 (7#6))
  | 35 => .base (.SLLI .x10 .x6 (6#6))
  | 36 => .base (.ADD .x7 .x7 .x10)
  | 37 => .base (.SLLI .x10 .x6 (3#6))
  | 38 => .base (.SUB .x7 .x7 .x10)
  | 39 => .base (.ANDI .x6 .x8 (1#12))
  | 40 => .base (.SLLI .x6 .x6 (4#6))
  | 41 => .base (.ADD .x7 .x7 .x6)
  | 42 => .base (.ADD .x10 .x18 .x7)
  | 43 => .base (.JAL .x1 (656#21))
  | 44 => .base (.DIVU .x22 .x8 .x19)
  | 45 => .base (.REMU .x23 .x8 .x19)
  | 46 => .base (.BEQ .x22 .x20 (88#13))
  | 47 => .base (.SLLI .x6 .x22 (6#6))
  | 48 => .base (.SLLI .x7 .x22 (5#6))
  | 49 => .base (.ADD .x28 .x6 .x7)
  | 50 => .base (.ADD .x28 .x9 .x28)
  | 51 => .base (.BEQ .x23 .x0 (32#13))
  | 52 => .base (.ADDI .x7 .x0 (1#12))
  | 53 => .base (.BEQ .x23 .x7 (44#13))
  | 54 => .base (.ADDI .x10 .x28 (0#12))
  | 55 => .base (.JAL .x1 (688#21))
  | 56 => .base (.ADDI .x10 .x28 (32#12))
  | 57 => .base (.JAL .x1 (680#21))
  | 58 => .base (.JAL .x0 (40#21))
  | 59 => .base (.ADDI .x10 .x28 (32#12))
  | 60 => .base (.JAL .x1 (668#21))
  | 61 => .base (.ADDI .x10 .x28 (64#12))
  | 62 => .base (.JAL .x1 (660#21))
  | 63 => .base (.JAL .x0 (20#21))
  | 64 => .base (.ADDI .x10 .x28 (0#12))
  | 65 => .base (.JAL .x1 (648#21))
  | 66 => .base (.ADDI .x10 .x28 (64#12))
  | 67 => .base (.JAL .x1 (640#21))
  | 68 => .base (.REMU .x23 .x22 .x19)
  | 69 => .base (.DIVU .x22 .x22 .x19)
  | 70 => .base (.ADDI .x6 .x0 (910#12))
  | 71 => .base (.SLLI .x6 .x6 (11#6))
  | 72 => .base (.ADDI .x6 .x6 (455#12))
  | 73 => .base (.BEQ .x22 .x6 (96#13))
  | 74 => .base (.SLLI .x6 .x22 (6#6))
  | 75 => .base (.SLLI .x7 .x22 (5#6))
  | 76 => .base (.ADD .x28 .x6 .x7)
  | 77 => .base (.LD .x6 .x2 (32#12))
  | 78 => .base (.ADD .x28 .x28 .x6)
  | 79 => .base (.ADD .x28 .x9 .x28)
  | 80 => .base (.BEQ .x23 .x0 (32#13))
  | 81 => .base (.ADDI .x7 .x0 (1#12))
  | 82 => .base (.BEQ .x23 .x7 (44#13))
  | 83 => .base (.ADDI .x10 .x28 (0#12))
  | 84 => .base (.JAL .x1 (572#21))
  | 85 => .base (.ADDI .x10 .x28 (32#12))
  | 86 => .base (.JAL .x1 (564#21))
  | 87 => .base (.JAL .x0 (40#21))
  | 88 => .base (.ADDI .x10 .x28 (32#12))
  | 89 => .base (.JAL .x1 (552#21))
  | 90 => .base (.ADDI .x10 .x28 (64#12))
  | 91 => .base (.JAL .x1 (544#21))
  | 92 => .base (.JAL .x0 (20#21))
  | 93 => .base (.ADDI .x10 .x28 (0#12))
  | 94 => .base (.JAL .x1 (532#21))
  | 95 => .base (.ADDI .x10 .x28 (64#12))
  | 96 => .base (.JAL .x1 (524#21))
  | 97 => .base (.ADDI .x29 .x2 (64#12))
  | 98 => .base (.ADDI .x30 .x2 (160#12))
  | 99 => .base (.XORI .x28 .x22 (1#12))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.LD .x7 .x29 (8#12))
  | 1 => .base (.BGEU .x28 .x7 (32#13))
  | 2 => .base (.SRLI .x6 .x28 (1#6))
  | 3 => .base (.ADD .x28 .x28 .x6)
  | 4 => .base (.SLLI .x28 .x28 (5#6))
  | 5 => .base (.LD .x6 .x29 (0#12))
  | 6 => .base (.ADD .x10 .x9 .x6)
  | 7 => .base (.ADD .x10 .x10 .x28)
  | 8 => .base (.JAL .x1 (476#21))
  | 9 => .base (.SRLI .x22 .x22 (1#6))
  | 10 => .base (.ADDI .x29 .x29 (32#12))
  | 11 => .base (.BNE .x29 .x30 (8144#13))
  | 12 => .base (.ADDI .x30 .x2 (288#12))
  | 13 => .base (.XORI .x28 .x22 (1#12))
  | 14 => .base (.LD .x7 .x29 (8#12))
  | 15 => .base (.BGEU .x28 .x7 (32#13))
  | 16 => .base (.SRLI .x6 .x28 (1#6))
  | 17 => .base (.ADD .x28 .x28 .x6)
  | 18 => .base (.SLLI .x28 .x28 (5#6))
  | 19 => .base (.LD .x6 .x29 (0#12))
  | 20 => .base (.ADD .x10 .x9 .x6)
  | 21 => .base (.ADD .x10 .x10 .x28)
  | 22 => .base (.JAL .x1 (524#21))
  | 23 => .base (.SRLI .x22 .x22 (1#6))
  | 24 => .base (.ADDI .x29 .x29 (32#12))
  | 25 => .base (.BNE .x29 .x30 (8144#13))
  | 26 => .base (.ADDI .x30 .x2 (448#12))
  | 27 => .base (.XORI .x28 .x22 (1#12))
  | 28 => .base (.LD .x7 .x29 (8#12))
  | 29 => .base (.BGEU .x28 .x7 (32#13))
  | 30 => .base (.SRLI .x6 .x28 (1#6))
  | 31 => .base (.ADD .x28 .x28 .x6)
  | 32 => .base (.SLLI .x28 .x28 (5#6))
  | 33 => .base (.LD .x6 .x29 (0#12))
  | 34 => .base (.ADD .x10 .x9 .x6)
  | 35 => .base (.ADD .x10 .x10 .x28)
  | 36 => .base (.JAL .x1 (604#21))
  | 37 => .base (.SRLI .x22 .x22 (1#6))
  | 38 => .base (.ADDI .x29 .x29 (32#12))
  | 39 => .base (.BNE .x29 .x30 (8144#13))
  | 40 => .base (.ADD .x6 .x21 .x22)
  | 41 => .base (.ADDI .x7 .x0 (1#12))
  | 42 => .base (.SB .x6 .x7 (0#12))
  | 43 => .base (.ADDI .x24 .x24 (8#12))
  | 44 => .base (.ADDI .x27 .x27 (4095#12))
  | 45 => .base (.BNE .x27 .x0 (7740#13))
  | 46 => .base (.ADDI .x29 .x2 (448#12))
  | 47 => .base (.ADDI .x30 .x2 (736#12))
  | 48 => .base (.LD .x18 .x29 (0#12))
  | 49 => .base (.ADD .x18 .x9 .x18)
  | 50 => .base (.LD .x19 .x29 (8#12))
  | 51 => .base (.LD .x20 .x29 (16#12))
  | 52 => .base (.ADD .x20 .x21 .x20)
  | 53 => .base (.LD .x22 .x29 (48#12))
  | 54 => .base (.ADD .x22 .x21 .x22)
  | 55 => .base (.SRLI .x23 .x19 (1#6))
  | 56 => .base (.ADDI .x24 .x0 (0#12))
  | 57 => .base (.SLLI .x6 .x24 (1#6))
  | 58 => .base (.ADD .x6 .x20 .x6)
  | 59 => .base (.LBU .x7 .x6 (0#12))
  | 60 => .base (.LBU .x8 .x6 (1#12))
  | 61 => .base (.OR .x11 .x7 .x8)
  | 62 => .base (.ADD .x6 .x22 .x24)
  | 63 => .base (.SB .x6 .x11 (0#12))
  | 64 => .base (.BEQ .x7 .x8 (32#13))
  | 65 => .base (.SLLI .x6 .x24 (6#6))
  | 66 => .base (.SLLI .x11 .x24 (5#6))
  | 67 => .base (.ADD .x10 .x6 .x11)
  | 68 => .base (.ADD .x10 .x18 .x10)
  | 69 => .base (.BEQ .x7 .x0 (8#13))
  | 70 => .base (.ADDI .x10 .x10 (32#12))
  | 71 => .base (.JAL .x1 (464#21))
  | 72 => .base (.ADDI .x24 .x24 (1#12))
  | 73 => .base (.BNE .x24 .x23 (8128#13))
  | 74 => .base (.ANDI .x6 .x19 (1#12))
  | 75 => .base (.BEQ .x6 .x0 (24#13))
  | 76 => .base (.SLLI .x7 .x23 (1#6))
  | 77 => .base (.ADD .x7 .x20 .x7)
  | 78 => .base (.LBU .x8 .x7 (0#12))
  | 79 => .base (.ADD .x7 .x22 .x23)
  | 80 => .base (.SB .x7 .x8 (0#12))
  | 81 => .base (.ADDI .x29 .x29 (32#12))
  | 82 => .base (.BNE .x29 .x30 (8056#13))
  | 83 => .base (.ADDI .x10 .x25 (0#12))
  | 84 => .base (.BEQ .x13 .x0 (24#13))
  | 85 => .base (.SB .x10 .x12 (0#12))
  | 86 => .base (.ADDI .x10 .x10 (1#12))
  | 87 => .base (.SRLI .x12 .x12 (8#6))
  | 88 => .base (.ADDI .x13 .x13 (4088#12))
  | 89 => .base (.BNE .x13 .x0 (8176#13))
  | 90 => .base (.BEQ .x17 .x0 (12#13))
  | 91 => .base (.SB .x15 .x16 (0#12))
  | 92 => .base (.ADDI .x15 .x15 (1#12))
  | 93 => .base (.BEQ .x15 .x31 (24#13))
  | 94 => .base (.ADDI .x15 .x15 (4095#12))
  | 95 => .base (.LBU .x6 .x15 (0#12))
  | 96 => .base (.SB .x10 .x6 (0#12))
  | 97 => .base (.ADDI .x10 .x10 (1#12))
  | 98 => .base (.BNE .x15 .x31 (8176#13))
  | 99 => .base (.SUB .x11 .x10 .x26)
  | _ => .base .EBREAK

private def openingInstr2 : Nat → Instruction
  | 0 => .base (.ADDI .x5 .x0 (1#12))
  | 1 => .base (.ADDI .x10 .x0 (0#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x11 .x0 (0#12))
  | 4 => .base (.ADDI .x5 .x0 (1#12))
  | 5 => .base (.ADDI .x10 .x0 (0#12))
  | 6 => .base .ECALL
  | 7 => .base (.LD .x5 .x10 (0#12))
  | 8 => .base (.SLL .x6 .x5 .x13)
  | 9 => .base (.OR .x12 .x12 .x6)
  | 10 => .base (.SD .x25 .x12 (0#12))
  | 11 => .base (.SRLI .x5 .x5 (1#6))
  | 12 => .base (.SRL .x12 .x5 .x14)
  | 13 => .base (.LD .x5 .x10 (8#12))
  | 14 => .base (.SLL .x6 .x5 .x13)
  | 15 => .base (.OR .x12 .x12 .x6)
  | 16 => .base (.SD .x25 .x12 (8#12))
  | 17 => .base (.SRLI .x5 .x5 (1#6))
  | 18 => .base (.SRL .x12 .x5 .x14)
  | 19 => .base (.LD .x5 .x10 (16#12))
  | 20 => .base (.SLL .x6 .x5 .x13)
  | 21 => .base (.OR .x12 .x12 .x6)
  | 22 => .base (.SD .x25 .x12 (16#12))
  | 23 => .base (.SRLI .x5 .x5 (1#6))
  | 24 => .base (.SRL .x12 .x5 .x14)
  | 25 => .base (.ADDI .x25 .x25 (24#12))
  | 26 => .base (.JALR .x0 .x1 (0#12))
  | 27 => .base (.LD .x5 .x10 (0#12))
  | 28 => .base (.SLL .x6 .x5 .x13)
  | 29 => .base (.OR .x12 .x12 .x6)
  | 30 => .base (.SD .x25 .x12 (0#12))
  | 31 => .base (.SRLI .x5 .x5 (1#6))
  | 32 => .base (.SRL .x12 .x5 .x14)
  | 33 => .base (.LD .x5 .x10 (8#12))
  | 34 => .base (.SLL .x6 .x5 .x13)
  | 35 => .base (.OR .x12 .x12 .x6)
  | 36 => .base (.SD .x25 .x12 (8#12))
  | 37 => .base (.SRLI .x5 .x5 (1#6))
  | 38 => .base (.SRL .x12 .x5 .x14)
  | 39 => .base (.LD .x5 .x10 (16#12))
  | 40 => .base (.SLL .x6 .x5 .x13)
  | 41 => .base (.OR .x12 .x12 .x6)
  | 42 => .base (.SD .x25 .x12 (16#12))
  | 43 => .base (.SRLI .x5 .x5 (1#6))
  | 44 => .base (.SRL .x12 .x5 .x14)
  | 45 => .base (.LD .x5 .x10 (24#12))
  | 46 => .base (.SLL .x6 .x5 .x13)
  | 47 => .base (.OR .x12 .x12 .x6)
  | 48 => .base (.SD .x25 .x12 (24#12))
  | 49 => .base (.SRLI .x5 .x5 (1#6))
  | 50 => .base (.SRL .x12 .x5 .x14)
  | 51 => .base (.ADDI .x25 .x25 (32#12))
  | 52 => .base (.JALR .x0 .x1 (0#12))
  | 53 => .base (.LD .x5 .x10 (0#12))
  | 54 => .base (.SLL .x6 .x5 .x13)
  | 55 => .base (.OR .x12 .x12 .x6)
  | 56 => .base (.SD .x25 .x12 (0#12))
  | 57 => .base (.SRLI .x5 .x5 (1#6))
  | 58 => .base (.SRL .x12 .x5 .x14)
  | 59 => .base (.LD .x5 .x10 (8#12))
  | 60 => .base (.SLL .x6 .x5 .x13)
  | 61 => .base (.OR .x12 .x12 .x6)
  | 62 => .base (.SD .x25 .x12 (8#12))
  | 63 => .base (.SRLI .x5 .x5 (1#6))
  | 64 => .base (.SRL .x12 .x5 .x14)
  | 65 => .base (.LD .x5 .x10 (16#12))
  | 66 => .base (.SLL .x6 .x5 .x13)
  | 67 => .base (.OR .x12 .x12 .x6)
  | 68 => .base (.SD .x25 .x12 (16#12))
  | 69 => .base (.SRLI .x5 .x5 (1#6))
  | 70 => .base (.SRL .x12 .x5 .x14)
  | 71 => .base (.ADDI .x25 .x25 (24#12))
  | 72 => .base (.LD .x5 .x10 (24#12))
  | 73 => .base (.SLLI .x5 .x5 (16#6))
  | 74 => .base (.SRLI .x5 .x5 (16#6))
  | 75 => .base (.SLL .x6 .x5 .x13)
  | 76 => .base (.OR .x12 .x12 .x6)
  | 77 => .base (.ADDI .x13 .x13 (48#12))
  | 78 => .base (.ADDI .x7 .x0 (64#12))
  | 79 => .base (.BLTU .x13 .x7 (24#13))
  | 80 => .base (.SD .x25 .x12 (0#12))
  | 81 => .base (.ADDI .x25 .x25 (8#12))
  | 82 => .base (.SRLI .x5 .x5 (1#6))
  | 83 => .base (.SRL .x12 .x5 .x14)
  | 84 => .base (.ADDI .x13 .x13 (4032#12))
  | 85 => .base (.XORI .x14 .x13 (63#12))
  | 86 => .base (.JALR .x0 .x1 (0#12))
  | 87 => .base (.LD .x5 .x10 (0#12))
  | 88 => .base (.SLL .x6 .x5 .x13)
  | 89 => .base (.OR .x12 .x12 .x6)
  | 90 => .base (.SD .x25 .x12 (0#12))
  | 91 => .base (.SRLI .x5 .x5 (1#6))
  | 92 => .base (.SRL .x12 .x5 .x14)
  | 93 => .base (.LD .x5 .x10 (8#12))
  | 94 => .base (.SLL .x6 .x5 .x13)
  | 95 => .base (.OR .x12 .x12 .x6)
  | 96 => .base (.SD .x25 .x12 (8#12))
  | 97 => .base (.SRLI .x5 .x5 (1#6))
  | 98 => .base (.SRL .x12 .x5 .x14)
  | 99 => .base (.LD .x5 .x10 (16#12))
  | _ => .base .EBREAK

private def openingInstr3 : Nat → Instruction
  | 0 => .base (.SLL .x6 .x5 .x13)
  | 1 => .base (.OR .x12 .x12 .x6)
  | 2 => .base (.SD .x25 .x12 (16#12))
  | 3 => .base (.SRLI .x5 .x5 (1#6))
  | 4 => .base (.SRL .x12 .x5 .x14)
  | 5 => .base (.ADDI .x25 .x25 (24#12))
  | 6 => .base (.LD .x11 .x10 (24#12))
  | 7 => .base (.SLLI .x5 .x11 (24#6))
  | 8 => .base (.SRLI .x5 .x5 (24#6))
  | 9 => .base (.SLL .x6 .x5 .x13)
  | 10 => .base (.OR .x12 .x12 .x6)
  | 11 => .base (.ADDI .x13 .x13 (40#12))
  | 12 => .base (.ADDI .x7 .x0 (64#12))
  | 13 => .base (.BLTU .x13 .x7 (24#13))
  | 14 => .base (.SD .x25 .x12 (0#12))
  | 15 => .base (.ADDI .x25 .x25 (8#12))
  | 16 => .base (.SRLI .x5 .x5 (1#6))
  | 17 => .base (.SRL .x12 .x5 .x14)
  | 18 => .base (.ADDI .x13 .x13 (4032#12))
  | 19 => .base (.XORI .x14 .x13 (63#12))
  | 20 => .base (.SRLI .x5 .x11 (40#6))
  | 21 => .base (.ANDI .x5 .x5 (63#12))
  | 22 => .base (.SLL .x6 .x5 .x17)
  | 23 => .base (.OR .x16 .x16 .x6)
  | 24 => .base (.ADDI .x17 .x17 (6#12))
  | 25 => .base (.ADDI .x7 .x0 (8#12))
  | 26 => .base (.BLTU .x17 .x7 (20#13))
  | 27 => .base (.SB .x15 .x16 (0#12))
  | 28 => .base (.ADDI .x15 .x15 (1#12))
  | 29 => .base (.SRLI .x16 .x16 (8#6))
  | 30 => .base (.ADDI .x17 .x17 (4088#12))
  | 31 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def openingInstr (idx : Nat) : Instruction :=
  if idx < 100 then openingInstr0 idx
  else if idx < 200 then openingInstr1 (idx - 100)
  else if idx < 300 then openingInstr2 (idx - 200)
  else openingInstr3 (idx - 300)

private theorem decode_opening_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr i.val) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (openingInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_opening_2 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (openingInstr (200 + i.val)) := by
  revert i; decide

private theorem decode_opening_3 (i : Fin 32) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨300 + i.val, by omega⟩) =
      some (openingInstr (300 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 332)
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
      by_cases h2 : idx < 300
      · have h := decode_opening_2 ⟨idx - 200, by omega⟩
        have heq : 200 + (idx - 200) = idx := by omega
        simpa only [heq] using h
      ·
        have h := decode_opening_3 ⟨idx - 300, by omega⟩
        have heq : 300 + (idx - 300) = idx := by omega
        simpa only [heq] using h

/-! ### Check Program (417 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (1504#13))
  | 8 => .base (.JAL .x0 (1488#21))
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
  | 24 => .base (.BLTU .x31 .x6 (1436#13))
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
  | 58 => .base (.JAL .x1 (1312#21))
  | 59 => .base (.JAL .x0 (20#21))
  | 60 => .base (.SD .x21 .x0 (120#12))
  | 61 => .base (.ADDI .x12 .x21 (96#12))
  | 62 => .base (.ADDI .x10 .x0 (24#12))
  | 63 => .base (.JAL .x1 (1292#21))
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
  | 77 => .base (.BLTU .x31 .x6 (1224#13))
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
  | 91 => .base (.JAL .x1 (1180#21))
  | 92 => .base (.JAL .x0 (76#21))
  | 93 => .base (.ADDI .x12 .x21 (32#12))
  | 94 => .base (.ADDI .x10 .x0 (64#12))
  | 95 => .base (.JAL .x1 (1164#21))
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
  | 7 => .base (.JAL .x1 (1116#21))
  | 8 => .base (.ADDI .x12 .x21 (64#12))
  | 9 => .base (.ADDI .x10 .x0 (32#12))
  | 10 => .base (.JAL .x1 (1104#21))
  | 11 => .base (.ADDI .x10 .x21 (0#12))
  | 12 => .base (.ADDI .x12 .x21 (0#12))
  | 13 => .base .ECALL
  | 14 => .base (.ADDI .x7 .x0 (3#12))
  | 15 => .base (.REMU .x23 .x22 .x7)
  | 16 => .base (.DIVU .x22 .x22 .x7)
  | 17 => .base (.ADDI .x6 .x0 (910#12))
  | 18 => .base (.SLLI .x6 .x6 (11#6))
  | 19 => .base (.ADDI .x6 .x6 (455#12))
  | 20 => .base (.BEQ .x22 .x6 (156#13))
  | 21 => .base (.ADDI .x6 .x25 (64#12))
  | 22 => .base (.BLTU .x31 .x6 (1044#13))
  | 23 => .base (.BEQ .x23 .x0 (60#13))
  | 24 => .base (.ADDI .x7 .x0 (1#12))
  | 25 => .base (.BEQ .x23 .x7 (68#13))
  | 26 => .base (.LD .x6 .x21 (0#12))
  | 27 => .base (.SD .x21 .x6 (64#12))
  | 28 => .base (.LD .x6 .x21 (8#12))
  | 29 => .base (.SD .x21 .x6 (72#12))
  | 30 => .base (.LD .x6 .x21 (16#12))
  | 31 => .base (.SD .x21 .x6 (80#12))
  | 32 => .base (.LD .x6 .x21 (24#12))
  | 33 => .base (.SD .x21 .x6 (88#12))
  | 34 => .base (.ADDI .x12 .x21 (0#12))
  | 35 => .base (.ADDI .x10 .x0 (64#12))
  | 36 => .base (.JAL .x1 (1000#21))
  | 37 => .base (.JAL .x0 (76#21))
  | 38 => .base (.ADDI .x12 .x21 (32#12))
  | 39 => .base (.ADDI .x10 .x0 (64#12))
  | 40 => .base (.JAL .x1 (984#21))
  | 41 => .base (.JAL .x0 (60#21))
  | 42 => .base (.LD .x6 .x21 (0#12))
  | 43 => .base (.SD .x21 .x6 (32#12))
  | 44 => .base (.LD .x6 .x21 (8#12))
  | 45 => .base (.SD .x21 .x6 (40#12))
  | 46 => .base (.LD .x6 .x21 (16#12))
  | 47 => .base (.SD .x21 .x6 (48#12))
  | 48 => .base (.LD .x6 .x21 (24#12))
  | 49 => .base (.SD .x21 .x6 (56#12))
  | 50 => .base (.ADDI .x12 .x21 (0#12))
  | 51 => .base (.ADDI .x10 .x0 (32#12))
  | 52 => .base (.JAL .x1 (936#21))
  | 53 => .base (.ADDI .x12 .x21 (64#12))
  | 54 => .base (.ADDI .x10 .x0 (32#12))
  | 55 => .base (.JAL .x1 (924#21))
  | 56 => .base (.ADDI .x10 .x21 (0#12))
  | 57 => .base (.ADDI .x12 .x21 (0#12))
  | 58 => .base .ECALL
  | 59 => .base (.SD .x21 .x0 (64#12))
  | 60 => .base (.SD .x21 .x0 (72#12))
  | 61 => .base (.SD .x21 .x0 (80#12))
  | 62 => .base (.SD .x21 .x0 (88#12))
  | 63 => .base (.ADDI .x29 .x2 (64#12))
  | 64 => .base (.ADDI .x30 .x2 (160#12))
  | 65 => .base (.XORI .x28 .x22 (1#12))
  | 66 => .base (.LD .x7 .x29 (8#12))
  | 67 => .base (.BGEU .x28 .x7 (104#13))
  | 68 => .base (.ADDI .x6 .x25 (32#12))
  | 69 => .base (.BLTU .x31 .x6 (856#13))
  | 70 => .base (.ANDI .x7 .x22 (1#12))
  | 71 => .base (.BEQ .x7 .x0 (52#13))
  | 72 => .base (.LD .x6 .x21 (0#12))
  | 73 => .base (.SD .x21 .x6 (32#12))
  | 74 => .base (.LD .x6 .x21 (8#12))
  | 75 => .base (.SD .x21 .x6 (40#12))
  | 76 => .base (.LD .x6 .x21 (16#12))
  | 77 => .base (.SD .x21 .x6 (48#12))
  | 78 => .base (.LD .x6 .x21 (24#12))
  | 79 => .base (.SD .x21 .x6 (56#12))
  | 80 => .base (.ADDI .x12 .x21 (0#12))
  | 81 => .base (.ADDI .x10 .x0 (32#12))
  | 82 => .base (.JAL .x1 (816#21))
  | 83 => .base (.JAL .x0 (16#21))
  | 84 => .base (.ADDI .x12 .x21 (32#12))
  | 85 => .base (.ADDI .x10 .x0 (32#12))
  | 86 => .base (.JAL .x1 (800#21))
  | 87 => .base (.ADDI .x10 .x21 (0#12))
  | 88 => .base (.ADDI .x12 .x21 (0#12))
  | 89 => .base .ECALL
  | 90 => .base (.ADDI .x6 .x2 (128#12))
  | 91 => .base (.BNE .x29 .x6 (8#13))
  | 92 => .base (.SH .x21 .x0 (30#12))
  | 93 => .base (.SRLI .x22 .x22 (1#6))
  | 94 => .base (.ADDI .x29 .x29 (32#12))
  | 95 => .base (.BNE .x29 .x30 (8072#13))
  | 96 => .base (.ADDI .x30 .x2 (288#12))
  | 97 => .base (.XORI .x28 .x22 (1#12))
  | 98 => .base (.LD .x7 .x29 (8#12))
  | 99 => .base (.BGEU .x28 .x7 (128#13))
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.ADDI .x6 .x25 (30#12))
  | 1 => .base (.BLTU .x31 .x6 (728#13))
  | 2 => .base (.ANDI .x7 .x22 (1#12))
  | 3 => .base (.BEQ .x7 .x0 (56#13))
  | 4 => .base (.LD .x6 .x21 (0#12))
  | 5 => .base (.SD .x21 .x6 (32#12))
  | 6 => .base (.LD .x6 .x21 (8#12))
  | 7 => .base (.SD .x21 .x6 (40#12))
  | 8 => .base (.LD .x6 .x21 (16#12))
  | 9 => .base (.SD .x21 .x6 (48#12))
  | 10 => .base (.LD .x6 .x21 (24#12))
  | 11 => .base (.SD .x21 .x6 (56#12))
  | 12 => .base (.ADDI .x12 .x21 (0#12))
  | 13 => .base (.ADDI .x10 .x0 (30#12))
  | 14 => .base (.JAL .x1 (688#21))
  | 15 => .base (.SH .x21 .x0 (30#12))
  | 16 => .base (.JAL .x0 (20#21))
  | 17 => .base (.ADDI .x12 .x21 (32#12))
  | 18 => .base (.ADDI .x10 .x0 (30#12))
  | 19 => .base (.JAL .x1 (668#21))
  | 20 => .base (.SH .x21 .x0 (62#12))
  | 21 => .base (.ADDI .x10 .x21 (0#12))
  | 22 => .base (.ADDI .x12 .x21 (0#12))
  | 23 => .base .ECALL
  | 24 => .base (.ADDI .x6 .x2 (256#12))
  | 25 => .base (.BEQ .x29 .x6 (12#13))
  | 26 => .base (.SH .x21 .x0 (30#12))
  | 27 => .base (.JAL .x0 (16#21))
  | 28 => .base (.LD .x6 .x21 (24#12))
  | 29 => .base (.AND .x6 .x6 .x9)
  | 30 => .base (.SD .x21 .x6 (24#12))
  | 31 => .base (.SRLI .x22 .x22 (1#6))
  | 32 => .base (.ADDI .x29 .x29 (32#12))
  | 33 => .base (.BNE .x29 .x30 (8048#13))
  | 34 => .base (.ADDI .x30 .x2 (448#12))
  | 35 => .base (.XORI .x28 .x22 (1#12))
  | 36 => .base (.LD .x7 .x29 (8#12))
  | 37 => .base (.BGEU .x28 .x7 (88#13))
  | 38 => .base (.ANDI .x7 .x22 (1#12))
  | 39 => .base (.BEQ .x7 .x0 (48#13))
  | 40 => .base (.LD .x6 .x21 (0#12))
  | 41 => .base (.SD .x21 .x6 (32#12))
  | 42 => .base (.LD .x6 .x21 (8#12))
  | 43 => .base (.SD .x21 .x6 (40#12))
  | 44 => .base (.LD .x6 .x21 (16#12))
  | 45 => .base (.SD .x21 .x6 (48#12))
  | 46 => .base (.LD .x6 .x21 (24#12))
  | 47 => .base (.SD .x21 .x6 (56#12))
  | 48 => .base (.ADDI .x12 .x21 (0#12))
  | 49 => .base (.JAL .x1 (576#21))
  | 50 => .base (.JAL .x0 (12#21))
  | 51 => .base (.ADDI .x12 .x21 (32#12))
  | 52 => .base (.JAL .x1 (564#21))
  | 53 => .base (.ADDI .x10 .x21 (0#12))
  | 54 => .base (.ADDI .x12 .x21 (0#12))
  | 55 => .base .ECALL
  | 56 => .base (.LD .x6 .x21 (24#12))
  | 57 => .base (.AND .x6 .x6 .x9)
  | 58 => .base (.SD .x21 .x6 (24#12))
  | 59 => .base (.SRLI .x22 .x22 (1#6))
  | 60 => .base (.ADDI .x29 .x29 (32#12))
  | 61 => .base (.BNE .x29 .x30 (8088#13))
  | 62 => .base (.SRLI .x6 .x22 (1#6))
  | 63 => .base (.ADD .x6 .x22 .x6)
  | 64 => .base (.SLLI .x6 .x6 (5#6))
  | 65 => .base (.ADD .x28 .x19 .x6)
  | 66 => .base (.ADD .x29 .x18 .x22)
  | 67 => .base (.LBU .x7 .x29 (0#12))
  | 68 => .base (.BNE .x7 .x0 (48#13))
  | 69 => .base (.ADDI .x7 .x0 (1#12))
  | 70 => .base (.SB .x29 .x7 (0#12))
  | 71 => .base (.LD .x6 .x21 (0#12))
  | 72 => .base (.SD .x28 .x6 (0#12))
  | 73 => .base (.LD .x6 .x21 (8#12))
  | 74 => .base (.SD .x28 .x6 (8#12))
  | 75 => .base (.LD .x6 .x21 (16#12))
  | 76 => .base (.SD .x28 .x6 (16#12))
  | 77 => .base (.LD .x6 .x21 (24#12))
  | 78 => .base (.SD .x28 .x6 (24#12))
  | 79 => .base (.JAL .x0 (52#21))
  | 80 => .base (.LD .x6 .x21 (0#12))
  | 81 => .base (.LD .x7 .x28 (0#12))
  | 82 => .base (.BNE .x6 .x7 (404#13))
  | 83 => .base (.LD .x6 .x21 (8#12))
  | 84 => .base (.LD .x7 .x28 (8#12))
  | 85 => .base (.BNE .x6 .x7 (392#13))
  | 86 => .base (.LD .x6 .x21 (16#12))
  | 87 => .base (.LD .x7 .x28 (16#12))
  | 88 => .base (.BNE .x6 .x7 (380#13))
  | 89 => .base (.LD .x6 .x21 (24#12))
  | 90 => .base (.LD .x7 .x28 (24#12))
  | 91 => .base (.BNE .x6 .x7 (368#13))
  | 92 => .base (.ADDI .x24 .x24 (8#12))
  | 93 => .base (.ADDI .x8 .x8 (256#12))
  | 94 => .base (.ADDI .x27 .x27 (4095#12))
  | 95 => .base (.BNE .x27 .x0 (7100#13))
  | 96 => .base (.ADDI .x29 .x2 (448#12))
  | 97 => .base (.ADDI .x30 .x2 (736#12))
  | 98 => .base (.LD .x20 .x29 (8#12))
  | 99 => .base (.LD .x14 .x29 (16#12))
  | _ => .base .EBREAK

private def checkInstr3 : Nat → Instruction
  | 0 => .base (.ADD .x14 .x18 .x14)
  | 1 => .base (.LD .x15 .x29 (48#12))
  | 2 => .base (.ADD .x15 .x18 .x15)
  | 3 => .base (.LD .x16 .x29 (24#12))
  | 4 => .base (.ADD .x16 .x19 .x16)
  | 5 => .base (.LD .x17 .x29 (56#12))
  | 6 => .base (.ADD .x17 .x19 .x17)
  | 7 => .base (.SRLI .x22 .x20 (1#6))
  | 8 => .base (.ADDI .x23 .x0 (0#12))
  | 9 => .base (.SLLI .x6 .x23 (1#6))
  | 10 => .base (.ADD .x6 .x14 .x6)
  | 11 => .base (.LBU .x7 .x6 (0#12))
  | 12 => .base (.LBU .x8 .x6 (1#12))
  | 13 => .base (.OR .x28 .x7 .x8)
  | 14 => .base (.BEQ .x28 .x0 (88#13))
  | 15 => .base (.ADD .x6 .x15 .x23)
  | 16 => .base (.SB .x6 .x28 (0#12))
  | 17 => .base (.SLLI .x6 .x23 (6#6))
  | 18 => .base (.SLLI .x28 .x23 (5#6))
  | 19 => .base (.ADD .x10 .x6 .x28)
  | 20 => .base (.ADD .x10 .x16 .x10)
  | 21 => .base (.BEQ .x7 .x8 (20#13))
  | 22 => .base (.ADDI .x12 .x10 (0#12))
  | 23 => .base (.BEQ .x7 .x0 (8#13))
  | 24 => .base (.ADDI .x12 .x10 (32#12))
  | 25 => .base (.JAL .x1 (272#21))
  | 26 => .base (.SRLI .x6 .x23 (1#6))
  | 27 => .base (.ADD .x6 .x23 .x6)
  | 28 => .base (.SLLI .x6 .x6 (5#6))
  | 29 => .base (.ADD .x12 .x17 .x6)
  | 30 => .base .ECALL
  | 31 => .base (.ADDI .x6 .x2 (704#12))
  | 32 => .base (.BEQ .x29 .x6 (16#13))
  | 33 => .base (.LD .x6 .x12 (24#12))
  | 34 => .base (.AND .x6 .x6 .x9)
  | 35 => .base (.SD .x12 .x6 (24#12))
  | 36 => .base (.ADDI .x23 .x23 (1#12))
  | 37 => .base (.BNE .x23 .x22 (8080#13))
  | 38 => .base (.ANDI .x6 .x20 (1#12))
  | 39 => .base (.BEQ .x6 .x0 (92#13))
  | 40 => .base (.SLLI .x7 .x22 (1#6))
  | 41 => .base (.ADD .x7 .x14 .x7)
  | 42 => .base (.LBU .x8 .x7 (0#12))
  | 43 => .base (.BEQ .x8 .x0 (76#13))
  | 44 => .base (.ADD .x7 .x15 .x22)
  | 45 => .base (.SB .x7 .x8 (0#12))
  | 46 => .base (.SLLI .x6 .x22 (6#6))
  | 47 => .base (.SLLI .x7 .x22 (5#6))
  | 48 => .base (.ADD .x10 .x6 .x7)
  | 49 => .base (.ADD .x10 .x16 .x10)
  | 50 => .base (.SRLI .x6 .x22 (1#6))
  | 51 => .base (.ADD .x6 .x22 .x6)
  | 52 => .base (.SLLI .x6 .x6 (5#6))
  | 53 => .base (.ADD .x12 .x17 .x6)
  | 54 => .base (.LD .x6 .x10 (0#12))
  | 55 => .base (.SD .x12 .x6 (0#12))
  | 56 => .base (.LD .x6 .x10 (8#12))
  | 57 => .base (.SD .x12 .x6 (8#12))
  | 58 => .base (.LD .x6 .x10 (16#12))
  | 59 => .base (.SD .x12 .x6 (16#12))
  | 60 => .base (.LD .x6 .x10 (24#12))
  | 61 => .base (.SD .x12 .x6 (24#12))
  | 62 => .base (.ADDI .x29 .x29 (32#12))
  | 63 => .base (.BNE .x29 .x30 (7932#13))
  | 64 => .base (.BNE .x25 .x31 (76#13))
  | 65 => .base (.BNE .x3 .x0 (72#13))
  | 66 => .base (.LD .x6 .x2 (760#12))
  | 67 => .base (.ADD .x10 .x19 .x6)
  | 68 => .base (.LD .x6 .x10 (0#12))
  | 69 => .base (.LD .x7 .x26 (0#12))
  | 70 => .base (.BNE .x6 .x7 (52#13))
  | 71 => .base (.LD .x6 .x10 (8#12))
  | 72 => .base (.LD .x7 .x26 (8#12))
  | 73 => .base (.BNE .x6 .x7 (40#13))
  | 74 => .base (.LD .x6 .x10 (16#12))
  | 75 => .base (.LD .x7 .x26 (16#12))
  | 76 => .base (.BNE .x6 .x7 (28#13))
  | 77 => .base (.LD .x6 .x10 (24#12))
  | 78 => .base (.LD .x7 .x26 (24#12))
  | 79 => .base (.BNE .x6 .x7 (16#13))
  | 80 => .base (.ADDI .x5 .x0 (1#12))
  | 81 => .base (.ADDI .x10 .x0 (0#12))
  | 82 => .base .ECALL
  | 83 => .base (.ADDI .x5 .x0 (1#12))
  | 84 => .base (.ADDI .x10 .x0 (1#12))
  | 85 => .base .ECALL
  | 86 => .base (.LBU .x6 .x25 (0#12))
  | 87 => .base (.SB .x12 .x6 (0#12))
  | 88 => .base (.ADDI .x25 .x25 (1#12))
  | 89 => .base (.ADDI .x12 .x12 (1#12))
  | 90 => .base (.ADDI .x10 .x10 (4095#12))
  | 91 => .base (.BNE .x10 .x0 (8172#13))
  | 92 => .base (.JALR .x0 .x1 (0#12))
  | 93 => .base (.ADDI .x6 .x25 (29#12))
  | 94 => .base (.BLTU .x31 .x6 (8148#13))
  | 95 => .base (.ADDI .x7 .x0 (29#12))
  | 96 => .base (.LBU .x6 .x25 (0#12))
  | 97 => .base (.SB .x12 .x6 (0#12))
  | 98 => .base (.ADDI .x25 .x25 (1#12))
  | 99 => .base (.ADDI .x12 .x12 (1#12))
  | _ => .base .EBREAK

private def checkInstr4 : Nat → Instruction
  | 0 => .base (.ADDI .x7 .x7 (4095#12))
  | 1 => .base (.BNE .x7 .x0 (8172#13))
  | 2 => .base (.ADDI .x7 .x0 (6#12))
  | 3 => .base (.BGEU .x4 .x7 (28#13))
  | 4 => .base (.BGEU .x25 .x31 (8108#13))
  | 5 => .base (.ADDI .x31 .x31 (4095#12))
  | 6 => .base (.LBU .x6 .x31 (0#12))
  | 7 => .base (.SLL .x6 .x6 .x4)
  | 8 => .base (.OR .x3 .x3 .x6)
  | 9 => .base (.ADDI .x4 .x4 (8#12))
  | 10 => .base (.ANDI .x6 .x3 (63#12))
  | 11 => .base (.SRLI .x3 .x3 (6#6))
  | 12 => .base (.ADDI .x4 .x4 (4090#12))
  | 13 => .base (.SB .x12 .x6 (0#12))
  | 14 => .base (.SB .x12 .x0 (1#12))
  | 15 => .base (.SB .x12 .x0 (2#12))
  | 16 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def checkInstr (idx : Nat) : Instruction :=
  if idx < 100 then checkInstr0 idx
  else if idx < 200 then checkInstr1 (idx - 100)
  else if idx < 300 then checkInstr2 (idx - 200)
  else if idx < 400 then checkInstr3 (idx - 300)
  else checkInstr4 (idx - 400)

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

private theorem decode_check_3 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨300 + i.val, by omega⟩) =
      some (checkInstr (300 + i.val)) := by
  revert i; decide

private theorem decode_check_4 (i : Fin 17) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨400 + i.val, by omega⟩) =
      some (checkInstr (400 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 417)
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
      by_cases h2 : idx < 300
      · have h := decode_check_2 ⟨idx - 200, by omega⟩
        have heq : 200 + (idx - 200) = idx := by omega
        simpa only [heq] using h
      ·
        by_cases h3 : idx < 400
        · have h := decode_check_3 ⟨idx - 300, by omega⟩
          have heq : 300 + (idx - 300) = idx := by omega
          simpa only [heq] using h
        ·
          have h := decode_check_4 ⟨idx - 400, by omega⟩
          have heq : 400 + (idx - 400) = idx := by omega
          simpa only [heq] using h

end CommitGolfCandidate
