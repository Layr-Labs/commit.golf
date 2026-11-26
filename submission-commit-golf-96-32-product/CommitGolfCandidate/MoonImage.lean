import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch, embedded-data, and admission proofs for the packed submission images.
Uses O(1) periodic block deduplication on `ArtifactEncoding.Packed` so large unrolls compile fast
at low RAM without O(N) `decide`. -/
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

/-- Generic O(1) lookup into any 8-way balanced `ArtifactEncoding.Packed` join of uniform size `S`. -/
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

/-! ### Fast Hierarchical Unwrapper for `MoonArtifact.commitCode` -/

private theorem get_commitCode_to_commitCode_2_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 32768) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_0.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_2_1 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 65536) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_1.get 32 ⟨idx - 32768, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_to_commitCode_2_2 (idx : Nat) (hlo : 65536 ≤ idx) (hhi : idx < 98304) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_2.get 32 ⟨idx - 65536, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_to_commitCode_2_3 (idx : Nat) (hlo : 98304 ≤ idx) (hhi : idx < 131072) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_3.get 32 ⟨idx - 98304, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_2_4 (idx : Nat) (hlo : 131072 ≤ idx) (hhi : idx < 148434) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_4.get 32 ⟨idx - 131072, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_4_to_commitCode_1_32 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 4096) :
    MoonArtifact.commitCode_2_4.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_32.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_4
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_4_to_commitCode_1_33 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 8192) :
    MoonArtifact.commitCode_2_4.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_33.get 32 ⟨idx - 4096, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_4
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_4_to_commitCode_1_34 (idx : Nat) (hlo : 8192 ≤ idx) (hhi : idx < 12288) :
    MoonArtifact.commitCode_2_4.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_34.get 32 ⟨idx - 8192, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_4
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_2_4_to_commitCode_1_35 (idx : Nat) (hlo : 12288 ≤ idx) (hhi : idx < 16384) :
    MoonArtifact.commitCode_2_4.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_35.get 32 ⟨idx - 12288, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_4
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_2_4_to_commitCode_1_36 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 17362) :
    MoonArtifact.commitCode_2_4.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_36.get 32 ⟨idx - 16384, by omega⟩ := by
  unfold MoonArtifact.commitCode_2_4
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
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_9 (idx : Nat) (hlo : 36864 ≤ idx) (hhi : idx < 40960) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_9.get 32 ⟨idx - 36864, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 1 := by omega
  rw [hqd, pick8_1]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_10 (idx : Nat) (hlo : 40960 ≤ idx) (hhi : idx < 45056) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_10.get 32 ⟨idx - 40960, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 2 := by omega
  rw [hqd, pick8_2]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_11 (idx : Nat) (hlo : 45056 ≤ idx) (hhi : idx < 49152) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_11.get 32 ⟨idx - 45056, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 3 := by omega
  rw [hqd, pick8_3]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_12 (idx : Nat) (hlo : 49152 ≤ idx) (hhi : idx < 53248) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_12.get 32 ⟨idx - 49152, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 4 := by omega
  rw [hqd, pick8_4]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_13 (idx : Nat) (hlo : 53248 ≤ idx) (hhi : idx < 57344) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_13.get 32 ⟨idx - 53248, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 5 := by omega
  rw [hqd, pick8_5]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_14 (idx : Nat) (hlo : 57344 ≤ idx) (hhi : idx < 61440) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_14.get 32 ⟨idx - 57344, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 6 := by omega
  rw [hqd, pick8_6]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_15 (idx : Nat) (hlo : 61440 ≤ idx) (hhi : idx < 65536) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_15.get 32 ⟨idx - 61440, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_2_1 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_8 MoonArtifact.commitCode_1_9) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_10 MoonArtifact.commitCode_1_11)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_12 MoonArtifact.commitCode_1_13) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_14 MoonArtifact.commitCode_1_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 4096 = 7 := by omega
  rw [hqd, pick8_7]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_16 (idx : Nat) (hlo : 65536 ≤ idx) (hhi : idx < 69632) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_16.get 32 ⟨idx - 65536, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_17 (idx : Nat) (hlo : 69632 ≤ idx) (hhi : idx < 73728) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_17.get 32 ⟨idx - 69632, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 1 := by omega
  rw [hqd, pick8_1]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_18 (idx : Nat) (hlo : 73728 ≤ idx) (hhi : idx < 77824) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_18.get 32 ⟨idx - 73728, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 2 := by omega
  rw [hqd, pick8_2]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_19 (idx : Nat) (hlo : 77824 ≤ idx) (hhi : idx < 81920) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_19.get 32 ⟨idx - 77824, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 3 := by omega
  rw [hqd, pick8_3]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_20 (idx : Nat) (hlo : 81920 ≤ idx) (hhi : idx < 86016) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_20.get 32 ⟨idx - 81920, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 4 := by omega
  rw [hqd, pick8_4]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_21 (idx : Nat) (hlo : 86016 ≤ idx) (hhi : idx < 90112) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_21.get 32 ⟨idx - 86016, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 5 := by omega
  rw [hqd, pick8_5]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_22 (idx : Nat) (hlo : 90112 ≤ idx) (hhi : idx < 94208) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_22.get 32 ⟨idx - 90112, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 6 := by omega
  rw [hqd, pick8_6]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_23 (idx : Nat) (hlo : 94208 ≤ idx) (hhi : idx < 98304) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_23.get 32 ⟨idx - 94208, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23 (idx - 65536) (by omega)
  have hdef : MoonArtifact.commitCode_2_2 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_16 MoonArtifact.commitCode_1_17) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_18 MoonArtifact.commitCode_1_19)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_20 MoonArtifact.commitCode_1_21) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_22 MoonArtifact.commitCode_1_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 65536) / 4096 = 7 := by omega
  rw [hqd, pick8_7]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_24 (idx : Nat) (hlo : 98304 ≤ idx) (hhi : idx < 102400) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_24.get 32 ⟨idx - 98304, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_25 (idx : Nat) (hlo : 102400 ≤ idx) (hhi : idx < 106496) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_25.get 32 ⟨idx - 102400, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 1 := by omega
  rw [hqd, pick8_1]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_26 (idx : Nat) (hlo : 106496 ≤ idx) (hhi : idx < 110592) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_26.get 32 ⟨idx - 106496, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 2 := by omega
  rw [hqd, pick8_2]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_27 (idx : Nat) (hlo : 110592 ≤ idx) (hhi : idx < 114688) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_27.get 32 ⟨idx - 110592, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 3 := by omega
  rw [hqd, pick8_3]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_28 (idx : Nat) (hlo : 114688 ≤ idx) (hhi : idx < 118784) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_28.get 32 ⟨idx - 114688, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 4 := by omega
  rw [hqd, pick8_4]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_29 (idx : Nat) (hlo : 118784 ≤ idx) (hhi : idx < 122880) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_29.get 32 ⟨idx - 118784, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 5 := by omega
  rw [hqd, pick8_5]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_30 (idx : Nat) (hlo : 122880 ≤ idx) (hhi : idx < 126976) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_30.get 32 ⟨idx - 122880, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 6 := by omega
  rw [hqd, pick8_6]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_31 (idx : Nat) (hlo : 126976 ≤ idx) (hhi : idx < 131072) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_31.get 32 ⟨idx - 126976, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31 (idx - 98304) (by omega)
  have hdef : MoonArtifact.commitCode_2_3 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_24 MoonArtifact.commitCode_1_25) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_26 MoonArtifact.commitCode_1_27)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_28 MoonArtifact.commitCode_1_29) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_30 MoonArtifact.commitCode_1_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 98304) / 4096 = 7 := by omega
  rw [hqd, pick8_7]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_32 (idx : Nat) (hlo : 131072 ≤ idx) (hhi : idx < 135168) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_32.get 32 ⟨idx - 131072, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_4 idx (by omega) (by omega)]
  rw [get_commitCode_2_4_to_commitCode_1_32 (idx - 131072) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_33 (idx : Nat) (hlo : 135168 ≤ idx) (hhi : idx < 139264) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_33.get 32 ⟨idx - 135168, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_4 idx (by omega) (by omega)]
  rw [get_commitCode_2_4_to_commitCode_1_33 (idx - 131072) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_34 (idx : Nat) (hlo : 139264 ≤ idx) (hhi : idx < 143360) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_34.get 32 ⟨idx - 139264, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_4 idx (by omega) (by omega)]
  rw [get_commitCode_2_4_to_commitCode_1_34 (idx - 131072) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_35 (idx : Nat) (hlo : 143360 ≤ idx) (hhi : idx < 147456) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_35.get 32 ⟨idx - 143360, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_4 idx (by omega) (by omega)]
  rw [get_commitCode_2_4_to_commitCode_1_35 (idx - 131072) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_36 (idx : Nat) (hlo : 147456 ≤ idx) (hhi : idx < 148434) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_36.get 32 ⟨idx - 147456, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_4 idx (by omega) (by omega)]
  rw [get_commitCode_2_4_to_commitCode_1_36 (idx - 131072) (by omega) (by omega)]
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

private abbrev randPair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 1454215873185275279712711993483803600776400284987587235380289567176129631896783066013677364507394967725806473094186230014761073616942096856900533110505735527190803171290397152489523045829967958523693620579249407650000965888808524663293849470607191213414153751619422819337118319693808770979540773659964359405944539563006134886354698134008765778424371243059484158360439813065232266706345911051077533570548419558686837439596323438212404321339911304560481347696665939791819936242231719451757093425714637035730359516418515664142066770997953714907842329592902399052195445057768617626809754012579830705827709545207872618611

private theorem randPair_chunk64_p0 (r : Fin 64) :
    randPair_c64_p0.get 32 r = randPairWord ((r.val + 0) % 2) := by
  revert r; decide

private theorem randPair_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_1.get 32 ⟨r, hr⟩ = randPairWord ((r + 0) % 2) := by
  have h8 := packed_get_join8 (S := 64) randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_1 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_1, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_2, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_3, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_4, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_5, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_6, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_7, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)

private theorem randPair_grp4096_p0 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_1.get 32 ⟨r, hr⟩ = randPairWord ((r + 0) % 2) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 r hr
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_8 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_9 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_10 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_11 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_12 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_13 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_14 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_15 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)

private theorem randPair_bnd64_0 (i : Fin 48) :
    (ArtifactEncoding.Packed.chunk 64 1454215873185275279712711993483803600776400284987587235380289567176129631896783066013677364507394967725806473094186230014761073616942096856900533110505735527190803171290397152489523045829967958523693620579249407650000965888808524663293849470607191213414153751619422819337118319693808770979540773659964359405944539563006134886354698134008765778424371243059484158360439813065232266706345911051077533570548419558686837439596323438212404321339911304560481347696665939209978451893993953140546345206450543126738195005063870080944644949399796109088585578713199528922851429086610634663230965621519294282864278390392742020115).get 32 ⟨16 + i.val, by omega⟩ =
      randPairWord ((0 + i.val) % 2) := by
  revert i; decide

private theorem randPair_bnd512_0 (r : Nat) (hlo : 16 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_0.get 32 ⟨r, by omega⟩ = randPairWord ((0 + r - 16) % 2) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 1454215873185275279712711993483803600776400284987587235380289567176129631896783066013677364507394967725806473094186230014761073616942096856900533110505735527190803171290397152489523045829967958523693620579249407650000965888808524663293849470607191213414153751619422819337118319693808770979540773659964359405944539563006134886354698134008765778424371243059484158360439813065232266706345911051077533570548419558686837439596323438212404321339911304560481347696665939209978451893993953140546345206450543126738195005063870080944644949399796109088585578713199528922851429086610634663230965621519294282864278390392742020115) randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 randPair_c64_p0 r (by omega)
  have hdef : MoonArtifact.commitCode_0_0 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 1454215873185275279712711993483803600776400284987587235380289567176129631896783066013677364507394967725806473094186230014761073616942096856900533110505735527190803171290397152489523045829967958523693620579249407650000965888808524663293849470607191213414153751619422819337118319693808770979540773659964359405944539563006134886354698134008765778424371243059484158360439813065232266706345911051077533570548419558686837439596323438212404321339911304560481347696665939209978451893993953140546345206450543126738195005063870080944644949399796109088585578713199528922851429086610634663230965621519294282864278390392742020115) randPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 randPair_c64_p0 randPair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := randPair_bnd64_0 ⟨r % 64 - 16, by omega⟩
    dsimp only at h
    have heq1 : 16 + (r % 64 - 16) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 16)) % 2 = (0 + r - 16) % 2 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_2, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_3, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_4, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_5, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_6, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)
  · rw [pick8_7, randPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg randPairWord (by dsimp only; omega)

private theorem randPair_bnd4096_0 (r : Nat) (hlo : 16 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_0.get 32 ⟨r, by omega⟩ = randPairWord ((0 + r - 16) % 2) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 r (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_bnd512_0 (r % 512) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_1 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_2 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_3 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_4 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_5 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_6 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_7 = MoonArtifact.commitCode_0_1 := rfl
    rw [hblk, randPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg randPairWord (by omega)

private theorem randPair_bnd64_256 (i : Fin 16) :
    (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091).get 32 ⟨0 + i.val, by omega⟩ =
      randPairWord ((16368 + i.val) % 2) := by
  revert i; decide

private theorem randPair_bnd512_32 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 16) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = randPairWord ((16384 + r - 16) % 2) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) r (by omega)
  have hdef : MoonArtifact.commitCode_0_32 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219) (ArtifactEncoding.Packed.chunk 64 507430512654353169647015562460893240448145362109216153736881337866418508235796660988433892352830436334052954684598501414449969795205973794530419754037835875724043395191413985136415755846737708471304992506093515541181242969103623292956053667754154862646072751734556646844944545110722863934965642691336341111887866604034694319466841705821897984215366008717549540184998925408227932386054728703218927724187675017725451098298379848877418509936045546010659703337854935486381044199919838423980392135526383845872421763644550226674983231568213713899530390709260741848839609828123678711427474964735150418145440730114643265043)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933080897823816647577235991864616458415109686054985703896488320805261865840582148805589409538704855606105486990985433856296792283329608567511719641465937507043738985168492612088835987438672377982214804996895819093448704650942954510601593231065909498029908210196781113278579) (ArtifactEncoding.Packed.chunk 64 2022288245532539079869265348038575234306723846503088119323388891326021741474691306600169238155494904470791468559123997350770312395929433286380483457381152652879022788923872850860504598820565989428145781274901606717679363742952180240255449409848292870984084380182006815340391740953744135403103877003923638398888134498135008305445059335366830437880162172095873366666756400756338081443241544642398702416108292158056423836508338805834684197318125597613858852311265644822015112177954058950527552804815551010441943111841712267596953605226339888346414782988779040135233835140990579002706079487435702089496610608563607635219)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := randPair_bnd64_256 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (16368 + (r % 64 - 0)) % 2 = (16384 + r - 16) % 2 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem randPair_bnd4096_4 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 16) :
    MoonArtifact.commitCode_1_4.get 32 ⟨r, by omega⟩ = randPairWord ((16384 + r - 16) % 2) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 r (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, randPair_bnd512_32 (r % 512) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_rand (state : MachineState) (k j : Nat) (hk : k < 8192) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (randPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (16 + 2 * k + j) (by omega)
    (randPairWord j) hpc _ (randPairInstr j) (decode_randPairWord ⟨j, hj⟩)
  have hg_lo : 0 ≤ (16 + 2 * k + j) / 4096 := by omega
  have hg_hi : (16 + 2 * k + j) / 4096 ≤ 4 := by omega
  generalize hgv : (16 + 2 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_0 (16 + 2 * k + j) (by omega) (by omega)]
    rw [randPair_bnd4096_0 (16 + 2 * k + j - 0) (by omega) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_1 (16 + 2 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_1 = MoonArtifact.commitCode_1_1 := rfl
    rw [hgrp, randPair_grp4096_p0 (16 + 2 * k + j - 4096) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_2 (16 + 2 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_2 = MoonArtifact.commitCode_1_1 := rfl
    rw [hgrp, randPair_grp4096_p0 (16 + 2 * k + j - 8192) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_3 (16 + 2 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_3 = MoonArtifact.commitCode_1_1 := rfl
    rw [hgrp, randPair_grp4096_p0 (16 + 2 * k + j - 12288) (by omega)]
    exact congrArg randPairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_4 (16 + 2 * k + j) (by omega) (by omega)]
    rw [randPair_bnd4096_4 (16 + 2 * k + j - 16384) (by omega) (by omega)]
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
    MoonArtifact.commitCode_0_34.get 32 ⟨r, hr⟩ = leaf0Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 r hr
  have hdef : MoonArtifact.commitCode_0_34 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1))) := rfl
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
    MoonArtifact.commitCode_0_33.get 32 ⟨r, hr⟩ = leaf0Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_33 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2))) := rfl
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
    MoonArtifact.commitCode_0_35.get 32 ⟨r, hr⟩ = leaf0Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_35 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0))) := rfl
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
    MoonArtifact.commitCode_1_5.get 32 ⟨r, hr⟩ = leaf0Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 r hr
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_40 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_41 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_42 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_43 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_44 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_45 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_46 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_47 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_grp4096_p1 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_6.get 32 ⟨r, hr⟩ = leaf0Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 r hr
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_48 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_49 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_50 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_51 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_52 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_53 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_54 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_55 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_grp4096_p2 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_7.get 32 ⟨r, hr⟩ = leaf0Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 r hr
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_56 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_57 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_58 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_59 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_60 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_61 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_62 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_63 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_bnd64_256 (i : Fin 36) :
    (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091).get 32 ⟨28 + i.val, by omega⟩ =
      leaf0Word ((0 + i.val) % 3) := by
  revert i; decide

private theorem leaf0_bnd512_32 (r : Nat) (hlo : 28 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = leaf0Word ((16384 + r - 16412) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091) leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 leaf0_c64_p1 leaf0_c64_p2 leaf0_c64_p0 r (by omega)
  have hdef : MoonArtifact.commitCode_0_32 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865422917696046687837657014550526013758853066800951464066451090737991444644993927650774502246055723810693393103010689547108067030110783385981262648523689805238571702650470185218474165781088343353480550788034187598939120393914723671484817029580593518675196763532215179078959899971339220845560424854500063386776492979008679760782569400537933081704228621355655644895604098552422197992793766303204276548243313739895310289755820476992364083634106590822285724012679342912648925212721869651787678704711729472648123127328343151790067569043334056621405655909569509573145172387289765869035592554699143858427287857791091) leaf0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p1 leaf0_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p0 leaf0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 leaf0_c64_p2 leaf0_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf0_bnd64_256 ⟨r % 64 - 28, by omega⟩
    dsimp only at h
    have heq1 : 28 + (r % 64 - 28) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 28)) % 3 = (16384 + r - 16412) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
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

private theorem leaf0_bnd4096_4 (r : Nat) (hlo : 28 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_4.get 32 ⟨r, by omega⟩ = leaf0Word ((16384 + r - 16412) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 r (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_bnd512_32 (r % 512) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_33 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_34 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_35 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_36 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_37 = MoonArtifact.commitCode_0_34 := rfl
    rw [hblk, leaf0_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_38 = MoonArtifact.commitCode_0_35 := rfl
    rw [hblk, leaf0_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_39 = MoonArtifact.commitCode_0_33 := rfl
    rw [hblk, leaf0_blk512_p1 (r % 512) (by omega)]
    exact congrArg leaf0Word (by omega)

private theorem leaf0_bnd64_640 (i : Fin 28) :
    (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339).get 32 ⟨0 + i.val, by omega⟩ =
      leaf0Word ((24548 + i.val) % 3) := by
  revert i; decide

private theorem leaf0_bnd512_80 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 28) :
    MoonArtifact.commitCode_0_80.get 32 ⟨r, by omega⟩ = leaf0Word ((40960 + r - 16412) % 3) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883) (ArtifactEncoding.Packed.chunk 64 759905195871952857195382297715854704407372522939729653910755925042705675695401160618942275779297465096892779202044748219168003245661686159102163236037381962163531335043520543331700956348657458140960781384558164718345496875074392057804361350792566552364777148929997014944577685795845288385587293094397240166500910958156045793810784291779274581579598854902479224619430290934147826170863775255372303284270133860340304787754823942895097297735485460005978460523520044003794041956108351753106693157232545666825229270074631203249963307684721624575061794531833804369849646404257237554328168109049847995784917266633949775123) (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074864734278607057210277800976859447271314807666821724464585450689738517852666579605139738524505839948846460965937376408296991335491460871833250617485540445118007989573182845799478987319952641086241393512907477082118238804233013672124336772883470351944973914736520239932649878580362398355145272235020825595293417058056432117111106053176231892726645450042791266598913555) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883) (ArtifactEncoding.Packed.chunk 64 759905195871952857195382297715854704407372522939729653910755925042705675695401160618942275779297465096892779202044748219168003245661686159102163236037381962163531335043520543331700956348657458140960781384558164718345496875074392057804361350792566552364777148929997014944577685795845288385587293094397240166500910958156045793810784291779274581579598854902479224619430290934147826170863775255372303284270133860340304787754823942895097297735485460005978460523520044003794041956108351753106693157232545666825229270074631203249963307684721624575061794531833804369849646404257237554328168109049847995784917266633949775123) (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074864734278607057210277800976859447271314807666821724464585450689738517852666579605139738524505839948846460965937376408296991335491460871833250617485540445118007989573182845799478987319952641086241393512907477082118238804233013672124336772883470351944973914736520239932649878580362398355145272235020825595293417058056432117111106053176231892726645450042791266598913555) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883) r (by omega)
  have hdef : MoonArtifact.commitCode_0_80 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857195382297715854704407372522939729653910755925042705675695401160618942275779297465096892779202044748219168003245661686159102163236037381962163531335043520543331700956348657458140960781384558164718345496875074392057804361350792566552364777148929997014944577685795845288385587293094397240166500910958156045793810784291779274581579598854902479224619430290934147826170863775255372303284270133860340304787754823942895097297735485460005978460523520044003794041956108351753106693157232545666825229270074631203249963307684721624575061794531833804369849646404257237554328168109049847995784917266633949775123) (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074864734278607057210277800976859447271314807666821724464585450689738517852666579605139738524505839948846460965937376408296991335491460871833250617485540445118007989573182845799478987319952641086241393512907477082118238804233013672124336772883470351944973914736520239932649878580362398355145272235020825595293417058056432117111106053176231892726645450042791266598913555))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883) (ArtifactEncoding.Packed.chunk 64 759905195871952857195382297715854704407372522939729653910755925042705675695401160618942275779297465096892779202044748219168003245661686159102163236037381962163531335043520543331700956348657458140960781384558164718345496875074392057804361350792566552364777148929997014944577685795845288385587293094397240166500910958156045793810784291779274581579598854902479224619430290934147826170863775255372303284270133860340304787754823942895097297735485460005978460523520044003794041956108351753106693157232545666825229270074631203249963307684721624575061794531833804369849646404257237554328168109049847995784917266633949775123)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074864734278607057210277800976859447271314807666821724464585450689738517852666579605139738524505839948846460965937376408296991335491460871833250617485540445118007989573182845799478987319952641086241393512907477082118238804233013672124336772883470351944973914736520239932649878580362398355145272235020825595293417058056432117111106053176231892726645450042791266598913555) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf0_bnd64_640 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (24548 + (r % 64 - 0)) % 3 = (40960 + r - 16412) % 3 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf0_bnd4096_10 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 28) :
    MoonArtifact.commitCode_1_10.get 32 ⟨r, by omega⟩ = leaf0Word ((40960 + r - 16412) % 3) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87 r (by omega)
  have hdef : MoonArtifact.commitCode_1_10 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf0_bnd512_80 (r % 512) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf0 (state : MachineState) (k j : Nat) (hk : k < 8192) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16412 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (leaf0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (16412 + 3 * k + j) (by omega)
    (leaf0Word j) hpc _ (leaf0Instr j) (decode_leaf0Word ⟨j, hj⟩)
  have hg_lo : 4 ≤ (16412 + 3 * k + j) / 4096 := by omega
  have hg_hi : (16412 + 3 * k + j) / 4096 ≤ 10 := by omega
  generalize hgv : (16412 + 3 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_4 (16412 + 3 * k + j) (by omega) (by omega)]
    rw [leaf0_bnd4096_4 (16412 + 3 * k + j - 16384) (by omega) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_5 (16412 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_5 = MoonArtifact.commitCode_1_5 := rfl
    rw [hgrp, leaf0_grp4096_p0 (16412 + 3 * k + j - 20480) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_6 (16412 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_6 = MoonArtifact.commitCode_1_6 := rfl
    rw [hgrp, leaf0_grp4096_p1 (16412 + 3 * k + j - 24576) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_7 (16412 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_7 = MoonArtifact.commitCode_1_7 := rfl
    rw [hgrp, leaf0_grp4096_p2 (16412 + 3 * k + j - 28672) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_8 (16412 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_8 = MoonArtifact.commitCode_1_5 := rfl
    rw [hgrp, leaf0_grp4096_p0 (16412 + 3 * k + j - 32768) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_9 (16412 + 3 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_9 = MoonArtifact.commitCode_1_6 := rfl
    rw [hgrp, leaf0_grp4096_p1 (16412 + 3 * k + j - 36864) (by omega)]
    exact congrArg leaf0Word (by omega)
  · rw [get_commitCode_to_commitCode_1_10 (16412 + 3 * k + j) (by omega) (by omega)]
    rw [leaf0_bnd4096_10 (16412 + 3 * k + j - 40960) (by omega) (by omega)]
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

private abbrev leaf12Pair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573272417538520404237627480588869760060109132115105199682784530079779288609919030665773948947738505041767110186868246378941422908547401393566363920520995154336797927130008087955557578196734933132806389797566583302795390783450238163711290711517169434806309324058677198903335120596324000800504759223303011269698103785955890587487133188674632764609110656997909394141232916820847921600308896257077676191907877989925383104709825156345962863539732081695988102438758720364864759482256492786265514265103829321265980175874977452638262425325499385831595725116895056190443773464494409429024883

private theorem leaf12Pair_chunk64_p2 (r : Fin 64) :
    leaf12Pair_c64_p2.get 32 r = leaf12PairWord ((r.val + 2) % 12) := by
  revert r; decide

private abbrev leaf12Pair_c64_p6 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857195382297715854704407372522939729653910755925042705675695401160618942275779297465096892779202044748219168003245661686159102163236037381962163531335043520543331700956348657458140960781384558164718345496875074392057804361350792566552364777148929997014944577685795845288385587293094397240166500910958156045793810784291779274581579598854902479224619430290934147826170863775255372303284270133860340304787754823942895097297735485460005978460523520044003794041956108351753106693157232545666825229270074631203249963307684721624575061794531833804369849646404257237554328168109049847995784917266633949775123

private theorem leaf12Pair_chunk64_p6 (r : Fin 64) :
    leaf12Pair_c64_p6.get 32 r = leaf12PairWord ((r.val + 6) % 12) := by
  revert r; decide

private abbrev leaf12Pair_c64_p10 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074864734278607057210277800976859447271314807666821724464585450689738517852666579605139738524505839948846460965937376408296991335491460871833250617485540445118007989573182845799478987319952641086241393512907477082118238804233013672124336772883470351944973914736520239932649878580362398355145272235020825595293417058056432117111106053176231892726645450042791266598913555

private theorem leaf12Pair_chunk64_p10 (r : Fin 64) :
    leaf12Pair_c64_p10.get 32 r = leaf12PairWord ((r.val + 10) % 12) := by
  revert r; decide

private theorem leaf12Pair_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_82.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 2) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 r hr
  have hdef : MoonArtifact.commitCode_0_82 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p2 leaf12Pair_c64_p6) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p10 leaf12Pair_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p6 leaf12Pair_c64_p10) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p2 leaf12Pair_c64_p6))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_blk512_p6 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_81.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 6) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 r hr
  have hdef : MoonArtifact.commitCode_0_81 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p6 leaf12Pair_c64_p10) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p2 leaf12Pair_c64_p6)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p10 leaf12Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p6 leaf12Pair_c64_p10))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_blk512_p10 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_83.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 10) % 12) := by
  have h8 := packed_get_join8 (S := 64) leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_83 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p10 leaf12Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p6 leaf12Pair_c64_p10)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p2 leaf12Pair_c64_p6) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p10 leaf12Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_grp4096_p2 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_11.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 2) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_88 MoonArtifact.commitCode_0_89 MoonArtifact.commitCode_0_90 MoonArtifact.commitCode_0_91 MoonArtifact.commitCode_0_92 MoonArtifact.commitCode_0_93 MoonArtifact.commitCode_0_94 MoonArtifact.commitCode_0_95 r hr
  have hdef : MoonArtifact.commitCode_1_11 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_88 MoonArtifact.commitCode_0_89) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_90 MoonArtifact.commitCode_0_91)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_92 MoonArtifact.commitCode_0_93) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_94 MoonArtifact.commitCode_0_95))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_88 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_89 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_90 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_91 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_92 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_93 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_94 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_95 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_grp4096_p6 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_12.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 6) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_96 MoonArtifact.commitCode_0_97 MoonArtifact.commitCode_0_98 MoonArtifact.commitCode_0_99 MoonArtifact.commitCode_0_100 MoonArtifact.commitCode_0_101 MoonArtifact.commitCode_0_102 MoonArtifact.commitCode_0_103 r hr
  have hdef : MoonArtifact.commitCode_1_12 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_96 MoonArtifact.commitCode_0_97) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_98 MoonArtifact.commitCode_0_99)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_100 MoonArtifact.commitCode_0_101) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_102 MoonArtifact.commitCode_0_103))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_96 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_97 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_98 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_99 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_100 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_101 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_102 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_103 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_grp4096_p10 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_13.get 32 ⟨r, hr⟩ = leaf12PairWord ((r + 10) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111 r hr
  have hdef : MoonArtifact.commitCode_1_13 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_104 MoonArtifact.commitCode_0_105) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_106 MoonArtifact.commitCode_0_107)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_108 MoonArtifact.commitCode_0_109) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_110 MoonArtifact.commitCode_0_111))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_104 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_105 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_106 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_107 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_108 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_109 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_110 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_111 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_bnd64_640 (i : Fin 26) :
    (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339).get 32 ⟨38 + i.val, by omega⟩ =
      leaf12PairWord ((0 + i.val) % 12) := by
  revert i; decide

private theorem leaf12Pair_bnd512_80 (r : Nat) (hlo : 38 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_80.get 32 ⟨r, by omega⟩ = leaf12PairWord ((40960 + r - 40998) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339) leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 leaf12Pair_c64_p6 leaf12Pair_c64_p10 leaf12Pair_c64_p2 r (by omega)
  have hdef : MoonArtifact.commitCode_0_80 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020924656716809291099214163695529260123049613567440209206336937573748500737476558479848080671879829664773886616620486977565522520655260895971666490393142678388020052703100784677283711247067934294155040526717482836232304591989872012983010680074866456748827929606265708028522778707645488643211016769990555898919029130440685005449573614929720531567056282590799833422269044039570637791461857938973062123857298886144939880323457439265425994944774368723970673325187212640964564435504815529999861353475807779468542709884645582185014402274166155652822966145607923297921312761853887770021384344374131233193400387764339) leaf12Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p6 leaf12Pair_c64_p10)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p2 leaf12Pair_c64_p6) (@ArtifactEncoding.Packed.join 64 64 leaf12Pair_c64_p10 leaf12Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf12Pair_bnd64_640 ⟨r % 64 - 38, by omega⟩
    dsimp only at h
    have heq1 : 38 + (r % 64 - 38) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 38)) % 12 = (40960 + r - 40998) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf12Pair_chunk64_p6 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf12Pair_chunk64_p10 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf12Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf12PairWord (by dsimp only; omega)

private theorem leaf12Pair_bnd4096_10 (r : Nat) (hlo : 38 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_10.get 32 ⟨r, by omega⟩ = leaf12PairWord ((40960 + r - 40998) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87 r (by omega)
  have hdef : MoonArtifact.commitCode_1_10 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_80 MoonArtifact.commitCode_0_81) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_82 MoonArtifact.commitCode_0_83)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_84 MoonArtifact.commitCode_0_85) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_86 MoonArtifact.commitCode_0_87))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_bnd512_80 (r % 512) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_81 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_82 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_83 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_84 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_85 = MoonArtifact.commitCode_0_82 := rfl
    rw [hblk, leaf12Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_86 = MoonArtifact.commitCode_0_83 := rfl
    rw [hblk, leaf12Pair_blk512_p10 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_87 = MoonArtifact.commitCode_0_81 := rfl
    rw [hblk, leaf12Pair_blk512_p6 (r % 512) (by omega)]
    exact congrArg leaf12PairWord (by omega)

private theorem leaf12Pair_bnd64_1408 (i : Fin 38) :
    (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459).get 32 ⟨0 + i.val, by omega⟩ =
      leaf12PairWord ((49114 + i.val) % 12) := by
  revert i; decide

private theorem leaf12Pair_bnd512_176 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 38) :
    MoonArtifact.commitCode_0_176.get 32 ⟨r, by omega⟩ = leaf12PairWord ((90112 + r - 40998) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331) (ArtifactEncoding.Packed.chunk 64 865364248217446317813108795363238783730618981219774788772489234175614396169412224482934496637973226634229127084453890641894036165686615931462941959706980661760902074200697960195924878637151024578166354626613961401178296852994056759837943004453269613283571907120464764865197570445813563589018543941804642085516459410713242317744405802453772213791623439805360793592056126792111681862643712297234124966132724043820690568697590038518076820797748160281676922403544879800082147628244123581694521171705271554842708054615566549430834248385257865093765017362413458117593537674070897072624273649252727558563859477299315) (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588544917004732348090611836421483033724163720757758185380121757498077344311908398510858669530025989440228902246869384356567212242732804134404156256844175385903045187160246776849381237631531128396561667544540146780767612157131353051645279738794463102879022109672654184601214723972195403403957927465098948521519785943875146355409374347626605681719758080368426154559731197388435751676144869835095374628507437538629324000000463737549305720011166477244137530098257822995) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331) (ArtifactEncoding.Packed.chunk 64 865364248217446317813108795363238783730618981219774788772489234175614396169412224482934496637973226634229127084453890641894036165686615931462941959706980661760902074200697960195924878637151024578166354626613961401178296852994056759837943004453269613283571907120464764865197570445813563589018543941804642085516459410713242317744405802453772213791623439805360793592056126792111681862643712297234124966132724043820690568697590038518076820797748160281676922403544879800082147628244123581694521171705271554842708054615566549430834248385257865093765017362413458117593537674070897072624273649252727558563859477299315) (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588544917004732348090611836421483033724163720757758185380121757498077344311908398510858669530025989440228902246869384356567212242732804134404156256844175385903045187160246776849381237631531128396561667544540146780767612157131353051645279738794463102879022109672654184601214723972195403403957927465098948521519785943875146355409374347626605681719758080368426154559731197388435751676144869835095374628507437538629324000000463737549305720011166477244137530098257822995) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331) r (by omega)
  have hdef : MoonArtifact.commitCode_0_176 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217446317813108795363238783730618981219774788772489234175614396169412224482934496637973226634229127084453890641894036165686615931462941959706980661760902074200697960195924878637151024578166354626613961401178296852994056759837943004453269613283571907120464764865197570445813563589018543941804642085516459410713242317744405802453772213791623439805360793592056126792111681862643712297234124966132724043820690568697590038518076820797748160281676922403544879800082147628244123581694521171705271554842708054615566549430834248385257865093765017362413458117593537674070897072624273649252727558563859477299315) (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588544917004732348090611836421483033724163720757758185380121757498077344311908398510858669530025989440228902246869384356567212242732804134404156256844175385903045187160246776849381237631531128396561667544540146780767612157131353051645279738794463102879022109672654184601214723972195403403957927465098948521519785943875146355409374347626605681719758080368426154559731197388435751676144869835095374628507437538629324000000463737549305720011166477244137530098257822995))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331) (ArtifactEncoding.Packed.chunk 64 865364248217446317813108795363238783730618981219774788772489234175614396169412224482934496637973226634229127084453890641894036165686615931462941959706980661760902074200697960195924878637151024578166354626613961401178296852994056759837943004453269613283571907120464764865197570445813563589018543941804642085516459410713242317744405802453772213791623439805360793592056126792111681862643712297234124966132724043820690568697590038518076820797748160281676922403544879800082147628244123581694521171705271554842708054615566549430834248385257865093765017362413458117593537674070897072624273649252727558563859477299315)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588544917004732348090611836421483033724163720757758185380121757498077344311908398510858669530025989440228902246869384356567212242732804134404156256844175385903045187160246776849381237631531128396561667544540146780767612157131353051645279738794463102879022109672654184601214723972195403403957927465098948521519785943875146355409374347626605681719758080368426154559731197388435751676144869835095374628507437538629324000000463737549305720011166477244137530098257822995) (ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf12Pair_bnd64_1408 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (49114 + (r % 64 - 0)) % 12 = (90112 + r - 40998) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf12Pair_bnd4096_22 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 38) :
    MoonArtifact.commitCode_1_22.get 32 ⟨r, by omega⟩ = leaf12PairWord ((90112 + r - 40998) % 12) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183 r (by omega)
  have hdef : MoonArtifact.commitCode_1_22 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf12Pair_bnd512_176 (r % 512) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf12 (state : MachineState) (k j : Nat) (hk : k < 4096) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (40998 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (leaf12PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (40998 + 12 * k + j) (by omega)
    (leaf12PairWord j) hpc _ (leaf12PairInstr j) (decode_leaf12PairWord ⟨j, hj⟩)
  have hg_lo : 10 ≤ (40998 + 12 * k + j) / 4096 := by omega
  have hg_hi : (40998 + 12 * k + j) / 4096 ≤ 22 := by omega
  generalize hgv : (40998 + 12 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_10 (40998 + 12 * k + j) (by omega) (by omega)]
    rw [leaf12Pair_bnd4096_10 (40998 + 12 * k + j - 40960) (by omega) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_11 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_11 = MoonArtifact.commitCode_1_11 := rfl
    rw [hgrp, leaf12Pair_grp4096_p2 (40998 + 12 * k + j - 45056) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_12 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_12 = MoonArtifact.commitCode_1_12 := rfl
    rw [hgrp, leaf12Pair_grp4096_p6 (40998 + 12 * k + j - 49152) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_13 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_13 = MoonArtifact.commitCode_1_13 := rfl
    rw [hgrp, leaf12Pair_grp4096_p10 (40998 + 12 * k + j - 53248) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_14 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_14 = MoonArtifact.commitCode_1_11 := rfl
    rw [hgrp, leaf12Pair_grp4096_p2 (40998 + 12 * k + j - 57344) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_15 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_15 = MoonArtifact.commitCode_1_12 := rfl
    rw [hgrp, leaf12Pair_grp4096_p6 (40998 + 12 * k + j - 61440) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_16 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_16 = MoonArtifact.commitCode_1_13 := rfl
    rw [hgrp, leaf12Pair_grp4096_p10 (40998 + 12 * k + j - 65536) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_17 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_17 = MoonArtifact.commitCode_1_11 := rfl
    rw [hgrp, leaf12Pair_grp4096_p2 (40998 + 12 * k + j - 69632) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_18 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_18 = MoonArtifact.commitCode_1_12 := rfl
    rw [hgrp, leaf12Pair_grp4096_p6 (40998 + 12 * k + j - 73728) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_19 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_19 = MoonArtifact.commitCode_1_13 := rfl
    rw [hgrp, leaf12Pair_grp4096_p10 (40998 + 12 * k + j - 77824) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_20 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_20 = MoonArtifact.commitCode_1_11 := rfl
    rw [hgrp, leaf12Pair_grp4096_p2 (40998 + 12 * k + j - 81920) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_21 (40998 + 12 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_21 = MoonArtifact.commitCode_1_12 := rfl
    rw [hgrp, leaf12Pair_grp4096_p6 (40998 + 12 * k + j - 86016) (by omega)]
    exact congrArg leaf12PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_22 (40998 + 12 * k + j) (by omega) (by omega)]
    rw [leaf12Pair_bnd4096_22 (40998 + 12 * k + j - 90112) (by omega) (by omega)]
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

private abbrev leaf3Pair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588544917004732348090611836421483033724163720757758185380121757498077344311908398510858669530025989440228902246869384356567212242732804134404156256844175385903045187160246776849381237631531128396561667544540146780767612157131353051645279738794463102879022109672654184601214723972195403403957927465098948521519785943875146355409374347626605681719758080368426154559731197388435751676144869835095374628507437538629324000000463737549305720011166477244137530098257822995

private theorem leaf3Pair_chunk64_p0 (r : Fin 64) :
    leaf3Pair_c64_p0.get 32 r = leaf3PairWord ((r.val + 0) % 6) := by
  revert r; decide

private abbrev leaf3Pair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217446317813108795363238783730618981219774788772489234175614396169412224482934496637973226634229127084453890641894036165686615931462941959706980661760902074200697960195924878637151024578166354626613961401178296852994056759837943004453269613283571907120464764865197570445813563589018543941804642085516459410713242317744405802453772213791623439805360793592056126792111681862643712297234124966132724043820690568697590038518076820797748160281676922403544879800082147628244123581694521171705271554842708054615566549430834248385257865093765017362413458117593537674070897072624273649252727558563859477299315

private theorem leaf3Pair_chunk64_p2 (r : Fin 64) :
    leaf3Pair_c64_p2.get 32 r = leaf3PairWord ((r.val + 2) % 6) := by
  revert r; decide

private abbrev leaf3Pair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020807088133613207435932721575728479997367797005954448871252596427524569878345592369503183732636378326554883635697974319852066916160377452040363786414153856460552626844212503433540944551129890454663407014186828569798320642169347582894273683181223493735615728451441972529346525523570936187266851721721601993273487931089276797607054586558124139684580073447200668250642378654314267906923604451241764859085201202304307330889702603190088690733671756924430485147573495378225059082786194007622975318509406767195773329704062007263784030477903841203339242208342863775119880826132412546116796220554179987449198475085331

private theorem leaf3Pair_chunk64_p4 (r : Fin 64) :
    leaf3Pair_c64_p4.get 32 r = leaf3PairWord ((r.val + 4) % 6) := by
  revert r; decide

private theorem leaf3Pair_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_179.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 r hr
  have hdef : MoonArtifact.commitCode_0_179 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p0 leaf3Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p2 leaf3Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p4 leaf3Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p0 leaf3Pair_c64_p4))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_177.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_177 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p2 leaf3Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p4 leaf3Pair_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p0 leaf3Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p2 leaf3Pair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_blk512_p4 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_178.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 64) leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_178 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p4 leaf3Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p0 leaf3Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p2 leaf3Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p4 leaf3Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_1, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_grp4096_p0 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_25.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_200 MoonArtifact.commitCode_0_201 MoonArtifact.commitCode_0_202 MoonArtifact.commitCode_0_203 MoonArtifact.commitCode_0_204 MoonArtifact.commitCode_0_205 MoonArtifact.commitCode_0_206 MoonArtifact.commitCode_0_207 r hr
  have hdef : MoonArtifact.commitCode_1_25 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_200 MoonArtifact.commitCode_0_201) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_202 MoonArtifact.commitCode_0_203)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_204 MoonArtifact.commitCode_0_205) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_206 MoonArtifact.commitCode_0_207))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_200 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_201 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_202 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_203 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_204 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_205 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_206 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_207 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_grp4096_p2 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_24.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_192 MoonArtifact.commitCode_0_193 MoonArtifact.commitCode_0_194 MoonArtifact.commitCode_0_195 MoonArtifact.commitCode_0_196 MoonArtifact.commitCode_0_197 MoonArtifact.commitCode_0_198 MoonArtifact.commitCode_0_199 r hr
  have hdef : MoonArtifact.commitCode_1_24 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_192 MoonArtifact.commitCode_0_193) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_194 MoonArtifact.commitCode_0_195)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_196 MoonArtifact.commitCode_0_197) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_198 MoonArtifact.commitCode_0_199))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_192 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_193 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_194 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_195 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_196 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_197 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_198 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_199 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_grp4096_p4 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_23.get 32 ⟨r, hr⟩ = leaf3PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_184 MoonArtifact.commitCode_0_185 MoonArtifact.commitCode_0_186 MoonArtifact.commitCode_0_187 MoonArtifact.commitCode_0_188 MoonArtifact.commitCode_0_189 MoonArtifact.commitCode_0_190 MoonArtifact.commitCode_0_191 r hr
  have hdef : MoonArtifact.commitCode_1_23 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_184 MoonArtifact.commitCode_0_185) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_186 MoonArtifact.commitCode_0_187)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_188 MoonArtifact.commitCode_0_189) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_190 MoonArtifact.commitCode_0_191))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_184 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_185 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_186 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_187 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_188 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_189 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_190 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_191 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_bnd64_1408 (i : Fin 16) :
    (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459).get 32 ⟨48 + i.val, by omega⟩ =
      leaf3PairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem leaf3Pair_bnd512_176 (r : Nat) (hlo : 48 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_176.get 32 ⟨r, by omega⟩ = leaf3PairWord ((90112 + r - 90160) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459) leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 leaf3Pair_c64_p2 leaf3Pair_c64_p0 leaf3Pair_c64_p4 r (by omega)
  have hdef : MoonArtifact.commitCode_0_176 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 696786043388923546037221681390282328583331645702142549346953480342126411579037806205952395112533349653841637125893244141502975880052883381494679652448588548780071038376907437742833530432590928885548515681080876224640190795738510972325645628044738232204446172773156911982426994724627799431719411526791889512965042335905415810131416178349440378308559328719346863715564302007016054075217083772715095950977352044746779747018006785270092375377841049812631178421227005471767438378025017260737879944430983148693267990210836636479762357138192212315055677350380399737156371022631761445101797088499450617151102951330245117459) leaf3Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p2 leaf3Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p4 leaf3Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 leaf3Pair_c64_p0 leaf3Pair_c64_p4))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf3Pair_bnd64_1408 ⟨r % 64 - 48, by omega⟩
    dsimp only at h
    have heq1 : 48 + (r % 64 - 48) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 48)) % 6 = (90112 + r - 90160) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_2, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_3, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_4, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_5, leaf3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_6, leaf3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)
  · rw [pick8_7, leaf3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg leaf3PairWord (by dsimp only; omega)

private theorem leaf3Pair_bnd4096_22 (r : Nat) (hlo : 48 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_22.get 32 ⟨r, by omega⟩ = leaf3PairWord ((90112 + r - 90160) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183 r (by omega)
  have hdef : MoonArtifact.commitCode_1_22 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_bnd512_176 (r % 512) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_177 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_178 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_179 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_180 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_181 = MoonArtifact.commitCode_0_178 := rfl
    rw [hblk, leaf3Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_182 = MoonArtifact.commitCode_0_179 := rfl
    rw [hblk, leaf3Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_183 = MoonArtifact.commitCode_0_177 := rfl
    rw [hblk, leaf3Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg leaf3PairWord (by omega)

private theorem leaf3Pair_bnd64_1792 (i : Fin 48) :
    (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499).get 32 ⟨0 + i.val, by omega⟩ =
      leaf3PairWord ((24528 + i.val) % 6) := by
  revert i; decide

private theorem leaf3Pair_bnd512_224 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 48) :
    MoonArtifact.commitCode_0_224.get 32 ⟨r, by omega⟩ = leaf3PairWord ((114688 + r - 90160) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) r (by omega)
  have hdef : MoonArtifact.commitCode_0_224 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755) (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883) (ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483) (ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := leaf3Pair_bnd64_1792 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (24528 + (r % 64 - 0)) % 6 = (114688 + r - 90160) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem leaf3Pair_bnd4096_28 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 48) :
    MoonArtifact.commitCode_1_28.get 32 ⟨r, by omega⟩ = leaf3PairWord ((114688 + r - 90160) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231 r (by omega)
  have hdef : MoonArtifact.commitCode_1_28 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, leaf3Pair_bnd512_224 (r % 512) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_leaf3 (state : MachineState) (k j : Nat) (hk : k < 4096) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (90160 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (leaf3PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (90160 + 6 * k + j) (by omega)
    (leaf3PairWord j) hpc _ (leaf3PairInstr j) (decode_leaf3PairWord ⟨j, hj⟩)
  have hg_lo : 22 ≤ (90160 + 6 * k + j) / 4096 := by omega
  have hg_hi : (90160 + 6 * k + j) / 4096 ≤ 28 := by omega
  generalize hgv : (90160 + 6 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_22 (90160 + 6 * k + j) (by omega) (by omega)]
    rw [leaf3Pair_bnd4096_22 (90160 + 6 * k + j - 90112) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_23 (90160 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_23 = MoonArtifact.commitCode_1_23 := rfl
    rw [hgrp, leaf3Pair_grp4096_p4 (90160 + 6 * k + j - 94208) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_24 (90160 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_24 = MoonArtifact.commitCode_1_24 := rfl
    rw [hgrp, leaf3Pair_grp4096_p2 (90160 + 6 * k + j - 98304) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_25 (90160 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_25 = MoonArtifact.commitCode_1_25 := rfl
    rw [hgrp, leaf3Pair_grp4096_p0 (90160 + 6 * k + j - 102400) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_26 (90160 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_26 = MoonArtifact.commitCode_1_23 := rfl
    rw [hgrp, leaf3Pair_grp4096_p4 (90160 + 6 * k + j - 106496) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_27 (90160 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_27 = MoonArtifact.commitCode_1_24 := rfl
    rw [hgrp, leaf3Pair_grp4096_p2 (90160 + 6 * k + j - 110592) (by omega)]
    exact congrArg leaf3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_28 (90160 + 6 * k + j) (by omega) (by omega)]
    rw [leaf3Pair_bnd4096_28 (90160 + 6 * k + j - 114688) (by omega) (by omega)]
    exact congrArg leaf3PairWord (by omega)

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

private abbrev l1Pair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195871952857185117209372349668640609265333240663454173617582426262794741908534102322435696018064148040841366773847449262687539857873579672140933922497745228924521660770015770507199567232120160627368292032196310084669955840649036268968912495975769769434497993060446580361172743518348106854421301286586420584516241639436081796653414608369774564327812472021452301327474493155444476494630792975286668003032981954852182748350250413362518279051083720148963853769525910425908595553564633145192733800733668369949978787362481346168114008468092245341906620219054591681979998861427477349249039664633776754550647634068755

private theorem l1Pair_chunk64_p0 (r : Fin 64) :
    l1Pair_c64_p0.get 32 r = l1PairWord ((r.val + 0) % 6) := by
  revert r; decide

private abbrev l1Pair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217449739509221172573273159500591783649781257881015868260483453784557725117971799789894523702445654990356128438402194224262252114365479139753513753047335558609839186668512511188642802118242852065866184247775472352174283611291519155260370828251197381079111770473390312442729963819359990383461043177372693133814983236087581029072828500776793100234253062642878349324702343646072144701195289033523132498961932542531406643769288365912929689702615854122936542764887368785928970022393580170815132575410533742038925100282555826355069800283499126369276896392126268817388961109731660391830695009437804048416883

private theorem l1Pair_chunk64_p2 (r : Fin 64) :
    l1Pair_c64_p2.get 32 r = l1PairWord ((r.val + 2) % 6) := by
  revert r; decide

private abbrev l1Pair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 507923630739205378150042410062955575419635039992880453747314975077167121063314075391225927160474298968391271954017877693615238349718769209102323075632772838472605215597037692393780077427162029129725209865174665735804215403493489999324477257366424249577578538028013582987908804528252823740525562998795289036632169497132973921564069858595609740511040412708812459856594222418486630340631850185607911374632777424810013413534588253562238847151979164150256911891739031229782358442181170954979149263325851078458984153784966101118583354927237858730370539697243454397675293818619253039210001411026651221551085122806415230483

private theorem l1Pair_chunk64_p4 (r : Fin 64) :
    l1Pair_c64_p4.get 32 r = l1PairWord ((r.val + 4) % 6) := by
  revert r; decide

private theorem l1Pair_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_225.get 32 ⟨r, hr⟩ = l1PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 64) l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 r hr
  have hdef : MoonArtifact.commitCode_0_225 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p0 l1Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p2 l1Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p4 l1Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p0 l1Pair_c64_p4))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_1, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_2, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_3, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_4, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_5, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_6, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_7, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)

private theorem l1Pair_blk512_p2 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_226.get 32 ⟨r, hr⟩ = l1PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 64) l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_226 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p2 l1Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p4 l1Pair_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p0 l1Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p2 l1Pair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_1, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_2, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_3, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_4, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_5, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_6, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_7, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)

private theorem l1Pair_blk512_p4 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_227.get 32 ⟨r, hr⟩ = l1PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 64) l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 r hr
  have hdef : MoonArtifact.commitCode_0_227 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p4 l1Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p0 l1Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p2 l1Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p4 l1Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_1, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_2, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_3, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_4, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_5, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_6, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_7, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)

private theorem l1Pair_grp4096_p0 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_30.get 32 ⟨r, hr⟩ = l1PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_240 MoonArtifact.commitCode_0_241 MoonArtifact.commitCode_0_242 MoonArtifact.commitCode_0_243 MoonArtifact.commitCode_0_244 MoonArtifact.commitCode_0_245 MoonArtifact.commitCode_0_246 MoonArtifact.commitCode_0_247 r hr
  have hdef : MoonArtifact.commitCode_1_30 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_240 MoonArtifact.commitCode_0_241) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_242 MoonArtifact.commitCode_0_243)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_244 MoonArtifact.commitCode_0_245) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_246 MoonArtifact.commitCode_0_247))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_240 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_241 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_242 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_243 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_244 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_245 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_246 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_247 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)

private theorem l1Pair_grp4096_p2 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_29.get 32 ⟨r, hr⟩ = l1PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_232 MoonArtifact.commitCode_0_233 MoonArtifact.commitCode_0_234 MoonArtifact.commitCode_0_235 MoonArtifact.commitCode_0_236 MoonArtifact.commitCode_0_237 MoonArtifact.commitCode_0_238 MoonArtifact.commitCode_0_239 r hr
  have hdef : MoonArtifact.commitCode_1_29 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_232 MoonArtifact.commitCode_0_233) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_234 MoonArtifact.commitCode_0_235)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_236 MoonArtifact.commitCode_0_237) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_238 MoonArtifact.commitCode_0_239))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_232 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_233 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_234 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_235 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_236 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_237 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_238 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_239 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)

private theorem l1Pair_grp4096_p4 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_31.get 32 ⟨r, hr⟩ = l1PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_248 MoonArtifact.commitCode_0_249 MoonArtifact.commitCode_0_250 MoonArtifact.commitCode_0_251 MoonArtifact.commitCode_0_252 MoonArtifact.commitCode_0_253 MoonArtifact.commitCode_0_254 MoonArtifact.commitCode_0_255 r hr
  have hdef : MoonArtifact.commitCode_1_31 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_248 MoonArtifact.commitCode_0_249) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_250 MoonArtifact.commitCode_0_251)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_252 MoonArtifact.commitCode_0_253) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_254 MoonArtifact.commitCode_0_255))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_248 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_249 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_250 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_251 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_252 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_253 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_254 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_255 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)

private theorem l1Pair_bnd64_1792 (i : Fin 2) :
    (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499).get 32 ⟨62 + i.val, by omega⟩ =
      l1PairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem l1Pair_bnd512_224 (r : Nat) (hlo : 62 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_224.get 32 ⟨r, by omega⟩ = l1PairWord ((114688 + r - 114750) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499) l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 l1Pair_c64_p0 l1Pair_c64_p4 l1Pair_c64_p2 r (by omega)
  have hdef : MoonArtifact.commitCode_0_224 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 507923630739205378152729942232001330545163530871001159538472262727150652971808861576065556740126097580092526414465021029114215947731493795010351821914015924866382773055208527301528255908760692152494186396725980082144738905180144203748758288760708805628824462642174992608627111419972957687365418113810961498239708354645678280198665647863645877568771292553907749095257432112271541322840925115746360418365201130726314588549212307294169421124011477107192657307015050464009089413443500555836662453440127264566030022488348113726954555412135061121796726973519806050697342451895964669548575323819842541373029601009750836499) l1Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p0 l1Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p2 l1Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1Pair_c64_p4 l1Pair_c64_p2))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := l1Pair_bnd64_1792 ⟨r % 64 - 62, by omega⟩
    dsimp only at h
    have heq1 : 62 + (r % 64 - 62) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 62)) % 6 = (114688 + r - 114750) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_1, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_2, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_3, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_4, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_5, l1Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_6, l1Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)
  · rw [pick8_7, l1Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg l1PairWord (by dsimp only; omega)

private theorem l1Pair_bnd4096_28 (r : Nat) (hlo : 62 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_28.get 32 ⟨r, by omega⟩ = l1PairWord ((114688 + r - 114750) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231 r (by omega)
  have hdef : MoonArtifact.commitCode_1_28 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Pair_bnd512_224 (r % 512) (by omega) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_225 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_226 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_227 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_228 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_229 = MoonArtifact.commitCode_0_226 := rfl
    rw [hblk, l1Pair_blk512_p2 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_230 = MoonArtifact.commitCode_0_227 := rfl
    rw [hblk, l1Pair_blk512_p4 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_231 = MoonArtifact.commitCode_0_225 := rfl
    rw [hblk, l1Pair_blk512_p0 (r % 512) (by omega)]
    exact congrArg l1PairWord (by omega)

private theorem l1Pair_bnd64_2176 (i : Fin 50) :
    (ArtifactEncoding.Packed.chunk 64 516376336698043919109474176031609644451883526274674762075906004046562814329762373047011781332136115748679364187006471424790639541600283941510785231093828069035199867671173698399632522287804354572724888663567998156328719488615712355319950299649516358825445940905890635761945651231369065435624502092197926801043279691759206807217489622324616658316680618568258625551917178068048738054587786547686561458883072464935535859157855429372366374987780231236949158428655378097223088299493117497257037908128336035707630291322106305946298152573695866069458347652887198310830157153903486850936804764437756388871761034006103571).get 32 ⟨0 + i.val, by omega⟩ =
      l1PairWord ((24514 + i.val) % 6) := by
  revert i; decide

private theorem l1Pair_bnd512_272 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 50) :
    MoonArtifact.commitCode_0_272.get 32 ⟨r, by omega⟩ = l1PairWord ((139264 + r - 114750) % 6) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 516376336698043919109474176031609644451883526274674762075906004046562814329762373047011781332136115748679364187006471424790639541600283941510785231093828069035199867671173698399632522287804354572724888663567998156328719488615712355319950299649516358825445940905890635761945651231369065435624502092197926801043279691759206807217489622324616658316680618568258625551917178068048738054587786547686561458883072464935535859157855429372366374987780231236949158428655378097223088299493117497257037908128336035707630291322106305946298152573695866069458347652887198310830157153903486850936804764437756388871761034006103571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841132583667824218646358828432323612115782236127228696887390535475033304374318896095153909704251873855180930794297874991361263234140155279624861357021662355) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) r (by omega)
  have hdef : MoonArtifact.commitCode_0_272 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 516376336698043919109474176031609644451883526274674762075906004046562814329762373047011781332136115748679364187006471424790639541600283941510785231093828069035199867671173698399632522287804354572724888663567998156328719488615712355319950299649516358825445940905890635761945651231369065435624502092197926801043279691759206807217489622324616658316680618568258625551917178068048738054587786547686561458883072464935535859157855429372366374987780231236949158428655378097223088299493117497257037908128336035707630291322106305946298152573695866069458347652887198310830157153903486850936804764437756388871761034006103571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841132583667824218646358828432323612115782236127228696887390535475033304374318896095153909704251873855180930794297874991361263234140155279624861357021662355)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have h := l1Pair_bnd64_2176 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (24514 + (r % 64 - 0)) % 6 = (139264 + r - 114750) % 6 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

private theorem l1Pair_bnd4096_34 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 50) :
    MoonArtifact.commitCode_1_34.get 32 ⟨r, by omega⟩ = l1PairWord ((139264 + r - 114750) % 6) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279 r (by omega)
  have hdef : MoonArtifact.commitCode_1_34 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1Pair_bnd512_272 (r % 512) (by omega) (by omega)]
    exact congrArg l1PairWord (by omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_l1_bulk (state : MachineState) (k j : Nat) (hk : k < 4094) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (114750 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (l1PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (114750 + 6 * k + j) (by omega)
    (l1PairWord j) hpc _ (l1PairInstr j) (decode_l1PairWord ⟨j, hj⟩)
  have hg_lo : 28 ≤ (114750 + 6 * k + j) / 4096 := by omega
  have hg_hi : (114750 + 6 * k + j) / 4096 ≤ 34 := by omega
  generalize hgv : (114750 + 6 * k + j) / 4096 = g at hg_lo hg_hi ⊢
  interval_cases g
  · rw [get_commitCode_to_commitCode_1_28 (114750 + 6 * k + j) (by omega) (by omega)]
    rw [l1Pair_bnd4096_28 (114750 + 6 * k + j - 114688) (by omega) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_29 (114750 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_29 = MoonArtifact.commitCode_1_29 := rfl
    rw [hgrp, l1Pair_grp4096_p2 (114750 + 6 * k + j - 118784) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_30 (114750 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_30 = MoonArtifact.commitCode_1_30 := rfl
    rw [hgrp, l1Pair_grp4096_p0 (114750 + 6 * k + j - 122880) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_31 (114750 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_31 = MoonArtifact.commitCode_1_31 := rfl
    rw [hgrp, l1Pair_grp4096_p4 (114750 + 6 * k + j - 126976) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_32 (114750 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_32 = MoonArtifact.commitCode_1_29 := rfl
    rw [hgrp, l1Pair_grp4096_p2 (114750 + 6 * k + j - 131072) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_33 (114750 + 6 * k + j) (by omega) (by omega)]
    have hgrp : MoonArtifact.commitCode_1_33 = MoonArtifact.commitCode_1_30 := rfl
    rw [hgrp, l1Pair_grp4096_p0 (114750 + 6 * k + j - 135168) (by omega)]
    exact congrArg l1PairWord (by omega)
  · rw [get_commitCode_to_commitCode_1_34 (114750 + 6 * k + j) (by omega) (by omega)]
    rw [l1Pair_bnd4096_34 (114750 + 6 * k + j - 139264) (by omega) (by omega)]
    exact congrArg l1PairWord (by omega)

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

private abbrev binPair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571

private theorem binPair_chunk64_p0 (r : Fin 64) :
    binPair_c64_p0.get 32 r = binPairWord ((r.val + 0) % 8) := by
  revert r; decide

private theorem binPair_blk512_p0 (r : Nat) (hr : r < 512) :
    MoonArtifact.commitCode_0_273.get 32 ⟨r, hr⟩ = binPairWord ((r + 0) % 8) := by
  have h8 := packed_get_join8 (S := 64) binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 r hr
  have hdef : MoonArtifact.commitCode_0_273 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_1, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_2, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_3, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_4, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_5, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_6, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_7, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)

private theorem binPair_grp4096_p0 (r : Nat) (hr : r < 4096) :
    MoonArtifact.commitCode_1_35.get 32 ⟨r, hr⟩ = binPairWord ((r + 0) % 8) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_280 MoonArtifact.commitCode_0_281 MoonArtifact.commitCode_0_282 MoonArtifact.commitCode_0_283 MoonArtifact.commitCode_0_284 MoonArtifact.commitCode_0_285 MoonArtifact.commitCode_0_286 MoonArtifact.commitCode_0_287 r hr
  have hdef : MoonArtifact.commitCode_1_35 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_280 MoonArtifact.commitCode_0_281) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_282 MoonArtifact.commitCode_0_283)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_284 MoonArtifact.commitCode_0_285) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_286 MoonArtifact.commitCode_0_287))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0]; have hblk : MoonArtifact.commitCode_0_280 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_281 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_282 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_283 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_284 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_285 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_286 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_287 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)

private theorem binPair_bnd64_2177 (i : Fin 48) :
    (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841132583667824218646358828432323612115782236127228696887390535475033304374318896095153909704251873855180930794297874991361263234140155279624861357021662355).get 32 ⟨16 + i.val, by omega⟩ =
      binPairWord ((0 + i.val) % 8) := by
  revert i; decide

private theorem binPair_bnd512_272 (r : Nat) (hlo : 80 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_272.get 32 ⟨r, by omega⟩ = binPairWord ((139264 + r - 139344) % 8) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 516376336698043919109474176031609644451883526274674762075906004046562814329762373047011781332136115748679364187006471424790639541600283941510785231093828069035199867671173698399632522287804354572724888663567998156328719488615712355319950299649516358825445940905890635761945651231369065435624502092197926801043279691759206807217489622324616658316680618568258625551917178068048738054587786547686561458883072464935535859157855429372366374987780231236949158428655378097223088299493117497257037908128336035707630291322106305946298152573695866069458347652887198310830157153903486850936804764437756388871761034006103571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841132583667824218646358828432323612115782236127228696887390535475033304374318896095153909704251873855180930794297874991361263234140155279624861357021662355) binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 binPair_c64_p0 r (by omega)
  have hdef : MoonArtifact.commitCode_0_272 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 516376336698043919109474176031609644451883526274674762075906004046562814329762373047011781332136115748679364187006471424790639541600283941510785231093828069035199867671173698399632522287804354572724888663567998156328719488615712355319950299649516358825445940905890635761945651231369065435624502092197926801043279691759206807217489622324616658316680618568258625551917178068048738054587786547686561458883072464935535859157855429372366374987780231236949158428655378097223088299493117497257037908128336035707630291322106305946298152573695866069458347652887198310830157153903486850936804764437756388871761034006103571) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841132583667824218646358828432323612115782236127228696887390535475033304374318896095153909704251873855180930794297874991361263234140155279624861357021662355)) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 binPair_c64_p0))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · rw [pick8_1]; have h := binPair_bnd64_2177 ⟨r % 64 - 16, by omega⟩
    dsimp only at h
    have heq1 : 16 + (r % 64 - 16) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 16)) % 8 = (139264 + r - 139344) % 8 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_2, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_3, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_4, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_5, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_6, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_7, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)

private theorem binPair_bnd4096_34 (r : Nat) (hlo : 80 ≤ r) (hhi : r < 4096) :
    MoonArtifact.commitCode_1_34.get 32 ⟨r, by omega⟩ = binPairWord ((139264 + r - 139344) % 8) := by
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279 r (by omega)
  have hdef : MoonArtifact.commitCode_1_34 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279))) := rfl
  rw [hdef, h8]
  have hq : r / 512 < 8 := by omega
  generalize hqv : r / 512 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, binPair_bnd512_272 (r % 512) (by omega) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_1]; have hblk : MoonArtifact.commitCode_0_273 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_2]; have hblk : MoonArtifact.commitCode_0_274 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_3]; have hblk : MoonArtifact.commitCode_0_275 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_4]; have hblk : MoonArtifact.commitCode_0_276 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_5]; have hblk : MoonArtifact.commitCode_0_277 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_6]; have hblk : MoonArtifact.commitCode_0_278 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)
  · rw [pick8_7]; have hblk : MoonArtifact.commitCode_0_279 = MoonArtifact.commitCode_0_273 := rfl
    rw [hblk, binPair_blk512_p0 (r % 512) (by omega)]
    exact congrArg binPairWord (by omega)

private theorem get_commitCode_1_36_to_commitCode_0_288 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 512) :
    MoonArtifact.commitCode_1_36.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_288.get 32 ⟨idx - 0, by omega⟩ := by
  unfold MoonArtifact.commitCode_1_36
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_288 (idx : Nat) (hlo : 147456 ≤ idx) (hhi : idx < 147968) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_288.get 32 ⟨idx - 147456, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_36 idx (by omega) (by omega)]
  rw [get_commitCode_1_36_to_commitCode_0_288 (idx - 147456) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem binPair_bnd64_2305 (i : Fin 16) :
    (ArtifactEncoding.Packed.chunk 64 6015689069581667715892531042221236783494968331655113397941494087224064781393201698908547292767409120502971855206443551352936960658449030205044468256616309423788629246966556863751130696423955940421201481977341971421372398132308031990958225315952791921483206848042349528802423892193907346973608664047072639482528487087316062691127040687832733118504371803772746082884050543675506523576183463249383154205467445947636131093877571172366231642282628316445731494743230781238179005845016125365591691832449848745254997791265724839897070318699481777935765761052940651860195891306869336510938938715654653877546414286118913299).get 32 ⟨0 + i.val, by omega⟩ =
      binPairWord ((8176 + i.val) % 8) := by
  revert i; decide

private theorem binPair_bnd512_288 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 80) :
    MoonArtifact.commitCode_0_288.get 32 ⟨r, by omega⟩ = binPairWord ((147456 + r - 139344) % 8) := by
  have h8 := packed_get_join8 (S := 64) binPair_c64_p0 (ArtifactEncoding.Packed.chunk 64 6015689069581667715892531042221236783494968331655113397941494087224064781393201698908547292767409120502971855206443551352936960658449030205044468256616309423788629246966556863751130696423955940421201481977341971421372398132308031990958225315952791921483206848042349528802423892193907346973608664047072639482528487087316062691127040687832733118504371803772746082884050543675506523576183463249383154205467445947636131093877571172366231642282628316445731494743230781238179005845016125365591691832449848745254997791265724839897070318699481777935765761052940651860195891306869336510938938715654653877546414286118913299) (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363610089806761396953762029809360526237779775663505669847793420031777849869165574593751209817337449475374404597409638728893747) (ArtifactEncoding.Packed.chunk 64 759905195883690559421518187397355735966109240390799210208826667034049077513075406378931106414055250446025783141204329315307920987700964991312895514142217310269457907661062612117047134955781527728350665412107215807596806008274478203766406659622607231364964081551170895406323031606553717020928662402520304166539448437311286345032015246108781482537474745269919446708621222397708370803028842056498152084983154757765101145706138275199931527330929242788934667354713566840941710119292453905536283844712752721496955351941337621449589107774457329950300530397471935265378500185921058501920099502476979754655326258679935021827) (ArtifactEncoding.Packed.chunk 64 214728396576915184857363958217766747523478411376687143064769963737139949374158471928924909291157885070539174699525306599784875341858461993684630424402063858706664255555546512709649751447982786837293322928927342094910765994837339777308667373721217090323409391295149466238682216346734167645669022575191182309421924256618335610902055995255023760876354001713376788570429897207923418018081539557677385356638931085702428356215254034288916352863796270307017258873731606626153945661041023996177610343317303804952087056106172067846389873787214100692088819300172402868234068802401427130863112031629047599243646425953680623123) (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363613180815536147353041332225197603886087246004750304550712251028371813641093304015692656814482700881327043182190161524309027) (ArtifactEncoding.Packed.chunk 64 759905195883690559421518187397355735966109240390799210208826667034049077513075406378931106414055250446025783141204329315307920987700964991312895514142217310269457907661062612117047134955781527728350665412107215807596806008274478203766406659622607231364964081551170895406323031606553717020928662402520304166539448437311286345032015246108781482537474745269919446708621222397708370803028842056498152084983154757765101145706138275199931527330929242788934667354713566840941710119292453905536283844712752721496955351941337621449589107774457329950300530397471935265378500185921058501920099502476979754655326258679935021827) (ArtifactEncoding.Packed.chunk 64 214728396576915184857363958217766747523478411376687143064769963737139949374158471928924909291157885070539174699525306599784875341858461993684630424402063858706664255555546512709649751447982786837293322928927342094910765994837339777308667373721217090323409391295149466238682216346734167645669022575191182309421924256618335610902055995255023760876354001713376788570429897207923418018081539557677385356638931085702428356215254034288916352863796270307017258873731606626153945661041023996177610343317303804952087056106172067846389873787214100692088819300172402868234068802401427130863112031629047599243646425953680623123) r (by omega)
  have hdef : MoonArtifact.commitCode_0_288 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 binPair_c64_p0 (ArtifactEncoding.Packed.chunk 64 6015689069581667715892531042221236783494968331655113397941494087224064781393201698908547292767409120502971855206443551352936960658449030205044468256616309423788629246966556863751130696423955940421201481977341971421372398132308031990958225315952791921483206848042349528802423892193907346973608664047072639482528487087316062691127040687832733118504371803772746082884050543675506523576183463249383154205467445947636131093877571172366231642282628316445731494743230781238179005845016125365591691832449848745254997791265724839897070318699481777935765761052940651860195891306869336510938938715654653877546414286118913299)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363610089806761396953762029809360526237779775663505669847793420031777849869165574593751209817337449475374404597409638728893747) (ArtifactEncoding.Packed.chunk 64 759905195883690559421518187397355735966109240390799210208826667034049077513075406378931106414055250446025783141204329315307920987700964991312895514142217310269457907661062612117047134955781527728350665412107215807596806008274478203766406659622607231364964081551170895406323031606553717020928662402520304166539448437311286345032015246108781482537474745269919446708621222397708370803028842056498152084983154757765101145706138275199931527330929242788934667354713566840941710119292453905536283844712752721496955351941337621449589107774457329950300530397471935265378500185921058501920099502476979754655326258679935021827))) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 214728396576915184857363958217766747523478411376687143064769963737139949374158471928924909291157885070539174699525306599784875341858461993684630424402063858706664255555546512709649751447982786837293322928927342094910765994837339777308667373721217090323409391295149466238682216346734167645669022575191182309421924256618335610902055995255023760876354001713376788570429897207923418018081539557677385356638931085702428356215254034288916352863796270307017258873731606626153945661041023996177610343317303804952087056106172067846389873787214100692088819300172402868234068802401427130863112031629047599243646425953680623123) (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363613180815536147353041332225197603886087246004750304550712251028371813641093304015692656814482700881327043182190161524309027)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 759905195883690559421518187397355735966109240390799210208826667034049077513075406378931106414055250446025783141204329315307920987700964991312895514142217310269457907661062612117047134955781527728350665412107215807596806008274478203766406659622607231364964081551170895406323031606553717020928662402520304166539448437311286345032015246108781482537474745269919446708621222397708370803028842056498152084983154757765101145706138275199931527330929242788934667354713566840941710119292453905536283844712752721496955351941337621449589107774457329950300530397471935265378500185921058501920099502476979754655326258679935021827) (ArtifactEncoding.Packed.chunk 64 214728396576915184857363958217766747523478411376687143064769963737139949374158471928924909291157885070539174699525306599784875341858461993684630424402063858706664255555546512709649751447982786837293322928927342094910765994837339777308667373721217090323409391295149466238682216346734167645669022575191182309421924256618335610902055995255023760876354001713376788570429897207923418018081539557677385356638931085702428356215254034288916352863796270307017258873731606626153945661041023996177610343317303804952087056106172067846389873787214100692088819300172402868234068802401427130863112031629047599243646425953680623123)))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, binPair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg binPairWord (by dsimp only; omega)
  · rw [pick8_1]; have h := binPair_bnd64_2305 ⟨r % 64 - 0, by omega⟩
    dsimp only at h
    have heq1 : 0 + (r % 64 - 0) = r % 64 := by omega
    have heq2 : (8176 + (r % 64 - 0)) % 8 = (147456 + r - 139344) % 8 := by omega
    simp only [heq1, heq2] at h; exact h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_bin_bulk (state : MachineState) (k j : Nat) (hk : k < 1024) (hj : j < 8)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (139344 + 8 * k + j))) :
    fetch (submission.image .commit) state = some (binPairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (139344 + 8 * k + j) (by omega)
    (binPairWord j) hpc _ (binPairInstr j) (decode_binPairWord ⟨j, hj⟩)
  by_cases hfull : 139344 + 8 * k + j < 147456
  ·
    have hg_lo : 34 ≤ (139344 + 8 * k + j) / 4096 := by omega
    have hg_hi : (139344 + 8 * k + j) / 4096 ≤ 35 := by omega
    generalize hgv : (139344 + 8 * k + j) / 4096 = g at hg_lo hg_hi ⊢
    interval_cases g
    · rw [get_commitCode_to_commitCode_1_34 (139344 + 8 * k + j) (by omega) (by omega)]
      rw [binPair_bnd4096_34 (139344 + 8 * k + j - 139264) (by omega) (by omega)]
      exact congrArg binPairWord (by omega)
    · rw [get_commitCode_to_commitCode_1_35 (139344 + 8 * k + j) (by omega) (by omega)]
      have hgrp : MoonArtifact.commitCode_1_35 = MoonArtifact.commitCode_1_35 := rfl
      rw [hgrp, binPair_grp4096_p0 (139344 + 8 * k + j - 143360) (by omega)]
      exact congrArg binPairWord (by omega)
  ·
    have hb_lo : 288 ≤ (139344 + 8 * k + j) / 512 := by omega
    have hb_hi : (139344 + 8 * k + j) / 512 ≤ 288 := by omega
    generalize hbv : (139344 + 8 * k + j) / 512 = b at hb_lo hb_hi ⊢
    interval_cases b
    · rw [get_commitCode_to_commitCode_0_288 (139344 + 8 * k + j) (by omega) (by omega)]
      rw [binPair_bnd512_288 (139344 + 8 * k + j - 147456) (by omega) (by omega)]
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

private abbrev bin238Pair_c64_p3 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 759905195883690559421518187397355735966109240390799210208826667034049077513075406378931106414055250446025783141204329315307920987700964991312895514142217310269457907661062612117047134955781527728350665412107215807596806008274478203766406659622607231364964081551170895406323031606553717020928662402520304166539448437311286345032015246108781482537474745269919446708621222397708370803028842056498152084983154757765101145706138275199931527330929242788934667354713566840941710119292453905536283844712752721496955351941337621449589107774457329950300530397471935265378500185921058501920099502476979754655326258679935021827

private theorem bin238Pair_chunk64_p3 (r : Fin 64) :
    bin238Pair_c64_p3.get 32 r = bin238PairWord ((r.val + 3) % 12) := by
  revert r; decide

private abbrev bin238Pair_c64_p7 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 214728396576915184857363958217766747523478411376687143064769963737139949374158471928924909291157885070539174699525306599784875341858461993684630424402063858706664255555546512709649751447982786837293322928927342094910765994837339777308667373721217090323409391295149466238682216346734167645669022575191182309421924256618335610902055995255023760876354001713376788570429897207923418018081539557677385356638931085702428356215254034288916352863796270307017258873731606626153945661041023996177610343317303804952087056106172067846389873787214100692088819300172402868234068802401427130863112031629047599243646425953680623123

private theorem bin238Pair_chunk64_p7 (r : Fin 64) :
    bin238Pair_c64_p7.get 32 r = bin238PairWord ((r.val + 7) % 12) := by
  revert r; decide

private abbrev bin238Pair_c64_p11 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363613180815536147353041332225197603886087246004750304550712251028371813641093304015692656814482700881327043182190161524309027

private theorem bin238Pair_chunk64_p11 (r : Fin 64) :
    bin238Pair_c64_p11.get 32 r = bin238PairWord ((r.val + 11) % 12) := by
  revert r; decide

private theorem bin238Pair_bnd64_2306 (i : Fin 51) :
    (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363610089806761396953762029809360526237779775663505669847793420031777849869165574593751209817337449475374404597409638728893747).get 32 ⟨13 + i.val, by omega⟩ =
      bin238PairWord ((0 + i.val) % 12) := by
  revert i; decide

private theorem bin238Pair_bnd512_288 (r : Nat) (hlo : 141 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_288.get 32 ⟨r, by omega⟩ = bin238PairWord ((147456 + r - 147597) % 12) := by
  have h8 := packed_get_join8 (S := 64) (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 6015689069581667715892531042221236783494968331655113397941494087224064781393201698908547292767409120502971855206443551352936960658449030205044468256616309423788629246966556863751130696423955940421201481977341971421372398132308031990958225315952791921483206848042349528802423892193907346973608664047072639482528487087316062691127040687832733118504371803772746082884050543675506523576183463249383154205467445947636131093877571172366231642282628316445731494743230781238179005845016125365591691832449848745254997791265724839897070318699481777935765761052940651860195891306869336510938938715654653877546414286118913299) (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363610089806761396953762029809360526237779775663505669847793420031777849869165574593751209817337449475374404597409638728893747) bin238Pair_c64_p3 bin238Pair_c64_p7 bin238Pair_c64_p11 bin238Pair_c64_p3 bin238Pair_c64_p7 r (by omega)
  have hdef : MoonArtifact.commitCode_0_288 = (@ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 3018687179948183347051990377678755027792731243316537023870207367231811903338593678597009588055886114311707557029272005637669610586927937552304511890845418858758212350158340175829276757972042592145604815309378230884124977400810750747026950986752713054047622556169993914115830246409724531548128526311105947697180602257945393667449801072333704500413233341699489722706753727708863570921110354447053952505365708811420291839539142860902632279902260519956374567103841113165043240401004676059518537204355691439769618518914366322053785029841090294805730612966416584683221083547615250056336473309301067363354317831738295571) (ArtifactEncoding.Packed.chunk 64 6015689069581667715892531042221236783494968331655113397941494087224064781393201698908547292767409120502971855206443551352936960658449030205044468256616309423788629246966556863751130696423955940421201481977341971421372398132308031990958225315952791921483206848042349528802423892193907346973608664047072639482528487087316062691127040687832733118504371803772746082884050543675506523576183463249383154205467445947636131093877571172366231642282628316445731494743230781238179005845016125365591691832449848745254997791265724839897070318699481777935765761052940651860195891306869336510938938715654653877546414286118913299)) (@ArtifactEncoding.Packed.join 64 64 (ArtifactEncoding.Packed.chunk 64 865423032509047781340862529935286691513389649702043099119204691664361985654765104186323854379294537307126456971247416636532183857881817909915637749884695014868085382261067124127869430668800287352640157769899467320102277421936449377512276835249206749980590969019360009281891320160841747683667833623004176734161125836800289342119746053470976378745950893582091083808487760160327527417371580848714695755479283492854535863674759637941833529343728260081861424897616105208781285855324701727363610089806761396953762029809360526237779775663505669847793420031777849869165574593751209817337449475374404597409638728893747) bin238Pair_c64_p3)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p7 bin238Pair_c64_p11) (@ArtifactEncoding.Packed.join 64 64 bin238Pair_c64_p3 bin238Pair_c64_p7))) := rfl
  rw [hdef, h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · omega
  · rw [pick8_2]; have h := bin238Pair_bnd64_2306 ⟨r % 64 - 13, by omega⟩
    dsimp only at h
    have heq1 : 13 + (r % 64 - 13) = r % 64 := by omega
    have heq2 : (0 + (r % 64 - 13)) % 12 = (147456 + r - 147597) % 12 := by omega
    simp only [heq1, heq2] at h; exact h
  · rw [pick8_3, bin238Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_4, bin238Pair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_5, bin238Pair_chunk64_p11 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_6, bin238Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)
  · rw [pick8_7, bin238Pair_chunk64_p7 ⟨r % 64, by omega⟩]
    exact congrArg bin238PairWord (by dsimp only; omega)

private theorem get_commitCode_1_36_to_commitCode_0_289 (idx : Nat) (hlo : 512 ≤ idx) (hhi : idx < 978) :
    MoonArtifact.commitCode_1_36.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_289.get 32 ⟨idx - 512, by omega⟩ := by
  unfold MoonArtifact.commitCode_1_36
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]

private theorem get_commitCode_to_commitCode_0_289 (idx : Nat) (hlo : 147968 ≤ idx) (hhi : idx < 148434) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_289.get 32 ⟨idx - 147968, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_36 idx (by omega) (by omega)]
  rw [get_commitCode_1_36_to_commitCode_0_289 (idx - 147456) (by omega) (by omega)]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem bin238Pair_bnd64_2318 (i : Fin 13) :
    (ArtifactEncoding.Packed.chunk 64 7323306964882679605408834372625482061221793973779925258786829708972484834488060637424920741370423165836816993618731636307849341799944456645361194081414900450658037512358198360723639172348222076711878760338248904254374301956665315340732156776263624804033974308842259129858423692175458642262361229551520422435030670795712069784954022287282400801128274202511024253609689288554129330134970355417250725753934807850742138142163482024749409312137339427537716858887235120461046890889883853521270412687614142411199944145830297992386587925844196505315231153102808754579091892872631778554119185567875124423588763507157736242211).get 32 ⟨0 + i.val, by omega⟩ =
      bin238PairWord ((755 + i.val) % 12) := by
  revert i; decide

private theorem bin238Pair_bnd512_289 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 397) :
    MoonArtifact.commitCode_0_289.get 32 ⟨r, by omega⟩ = bin238PairWord ((147968 + r - 147597) % 12) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p11 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 11) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p3 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 3) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p7 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 7) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p11 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 11) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p3 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 3) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_chunk64_p7 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 7) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_289
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := bin238Pair_bnd64_2318 ⟨r - 384 - 0, by omega⟩
    dsimp only at h
    have heq2 : (755 + (r - 384 - 0)) % 12 = (147968 + r - 147597) % 12 := by omega
    rw [← heq2, ← h]; exact packed_get_congr _ (by dsimp only; omega)
  · omega

theorem commit_fetch_bin238_bulk (state : MachineState) (k j : Nat) (hk : k < 64) (hj : j < 12)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (147597 + 12 * k + j))) :
    fetch (submission.image .commit) state = some (bin238PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (147597 + 12 * k + j) (by omega)
    (bin238PairWord j) hpc _ (bin238PairInstr j) (decode_bin238PairWord ⟨j, hj⟩)
  have hb_lo : 288 ≤ (147597 + 12 * k + j) / 512 := by omega
  have hb_hi : (147597 + 12 * k + j) / 512 ≤ 289 := by omega
  generalize hbv : (147597 + 12 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_288 (147597 + 12 * k + j) (by omega) (by omega)]
    rw [bin238Pair_bnd512_288 (147597 + 12 * k + j - 147456) (by omega) (by omega)]
    exact congrArg bin238PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_289 (147597 + 12 * k + j) (by omega) (by omega)]
    rw [bin238Pair_bnd512_289 (147597 + 12 * k + j - 147968) (by omega) (by omega)]
    exact congrArg bin238PairWord (by omega)

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

private theorem decode_commitPrefixInstr_b0 (i : Fin 16) :
    decodeInstruction (MoonArtifact.commitCode_0_0.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 16)
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
  | 16400 => .base (.BEQ .x10 .x19 (8#13))
  | 16401 => .base (.JAL .x0 (2031612#21))
  | 16402 => .base (.ADDI .x5 .x0 (0#12))
  | 16403 => .base (.ADDI .x11 .x0 (96#12))
  | 16404 => .base (.ADDI .x13 .x0 (0#12))
  | 16405 => .base (.ADDI .x10 .x8 (3840#12))
  | 16406 => .base (.ADDI .x6 .x0 (1023#12))
  | 16407 => .base (.SLLI .x6 .x6 (11#6))
  | 16408 => .base (.ADDI .x6 .x6 (2047#12))
  | 16409 => .base (.SLLI .x6 .x6 (11#6))
  | 16410 => .base (.ADDI .x6 .x6 (1792#12))
  | 16411 => .base (.ADD .x19 .x8 .x6)
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

private theorem decode_commitMid0Instr_b32 (i : Fin 12) :
    decodeInstruction (MoonArtifact.commitCode_0_32.get 32 ⟨16 + i.val, by omega⟩) =
      some (commitMid0Instr (16400 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 16400 ≤ idx) (hhi : idx < 16412)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_32 idx (by omega) (by omega)]
  have h := decode_commitMid0Instr_b32 ⟨idx - 16400, by omega⟩
  dsimp only at h
  have heq1 : 16 + (idx - 16400) = idx - 16384 := by omega
  have heq2 : 16400 + (idx - 16400) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1AInstr : Nat → Instruction
  | 40988 => .base (.BEQ .x10 .x19 (8#13))
  | 40989 => .base (.JAL .x0 (1998844#21))
  | 40990 => .base (.ADDI .x10 .x8 (4000#12))
  | 40991 => .base (.ADDI .x12 .x18 (4064#12))
  | 40992 => .base (.ADDI .x6 .x0 (1023#12))
  | 40993 => .base (.SLLI .x6 .x6 (11#6))
  | 40994 => .base (.ADDI .x6 .x6 (2047#12))
  | 40995 => .base (.SLLI .x6 .x6 (11#6))
  | 40996 => .base (.ADDI .x6 .x6 (1952#12))
  | 40997 => .base (.ADD .x19 .x8 .x6)
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

private theorem decode_commitMid1AInstr_b80 (i : Fin 10) :
    decodeInstruction (MoonArtifact.commitCode_0_80.get 32 ⟨28 + i.val, by omega⟩) =
      some (commitMid1AInstr (40988 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 40988 ≤ idx) (hhi : idx < 40998)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_80 idx (by omega) (by omega)]
  have h := decode_commitMid1AInstr_b80 ⟨idx - 40988, by omega⟩
  dsimp only at h
  have heq1 : 28 + (idx - 40988) = idx - 40960 := by omega
  have heq2 : 40988 + (idx - 40988) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1BInstr : Nat → Instruction
  | 90150 => .base (.BEQ .x10 .x19 (8#13))
  | 90151 => .base (.JAL .x0 (1900540#21))
  | 90152 => .base (.ADDI .x10 .x18 (4000#12))
  | 90153 => .base (.ADDI .x12 .x9 (4064#12))
  | 90154 => .base (.ADDI .x6 .x0 (367#12))
  | 90155 => .base (.SLLI .x6 .x6 (11#6))
  | 90156 => .base (.ADDI .x6 .x6 (2047#12))
  | 90157 => .base (.SLLI .x6 .x6 (11#6))
  | 90158 => .base (.ADDI .x6 .x6 (1952#12))
  | 90159 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_176 (idx : Nat) (hlo : 90112 ≤ idx) (hhi : idx < 90624) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_176.get 32 ⟨idx - 90112, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_22 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183 (idx - 90112) (by omega)
  have hdef : MoonArtifact.commitCode_1_22 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_176 MoonArtifact.commitCode_0_177) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_178 MoonArtifact.commitCode_0_179)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_180 MoonArtifact.commitCode_0_181) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_182 MoonArtifact.commitCode_0_183))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 90112) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid1BInstr_b176 (i : Fin 10) :
    decodeInstruction (MoonArtifact.commitCode_0_176.get 32 ⟨38 + i.val, by omega⟩) =
      some (commitMid1BInstr (90150 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 90150 ≤ idx) (hhi : idx < 90160)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_176 idx (by omega) (by omega)]
  have h := decode_commitMid1BInstr_b176 ⟨idx - 90150, by omega⟩
  dsimp only at h
  have heq1 : 38 + (idx - 90150) = idx - 90112 := by omega
  have heq2 : 90150 + (idx - 90150) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1CInstr : Nat → Instruction
  | 114736 => .base (.BEQ .x10 .x19 (8#13))
  | 114737 => .base (.JAL .x0 (1998844#21))
  | 114738 => .base (.ADDI .x10 .x9 (4000#12))
  | 114739 => .base (.ADDI .x6 .x0 (128#12))
  | 114740 => .base (.SLLI .x6 .x6 (11#6))
  | 114741 => .base (.SLLI .x6 .x6 (11#6))
  | 114742 => .base (.ADD .x12 .x9 .x6)
  | 114743 => .base (.ADDI .x12 .x12 (4032#12))
  | 114744 => .base (.ADDI .x6 .x0 (127#12))
  | 114745 => .base (.SLLI .x6 .x6 (11#6))
  | 114746 => .base (.ADDI .x6 .x6 (2047#12))
  | 114747 => .base (.SLLI .x6 .x6 (11#6))
  | 114748 => .base (.ADDI .x6 .x6 (1824#12))
  | 114749 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_224 (idx : Nat) (hlo : 114688 ≤ idx) (hhi : idx < 115200) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_224.get 32 ⟨idx - 114688, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_28 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231 (idx - 114688) (by omega)
  have hdef : MoonArtifact.commitCode_1_28 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_224 MoonArtifact.commitCode_0_225) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_226 MoonArtifact.commitCode_0_227)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_228 MoonArtifact.commitCode_0_229) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_230 MoonArtifact.commitCode_0_231))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 114688) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid1CInstr_b224 (i : Fin 14) :
    decodeInstruction (MoonArtifact.commitCode_0_224.get 32 ⟨48 + i.val, by omega⟩) =
      some (commitMid1CInstr (114736 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (hlo : 114736 ≤ idx) (hhi : idx < 114750)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_224 idx (by omega) (by omega)]
  have h := decode_commitMid1CInstr_b224 ⟨idx - 114736, by omega⟩
  dsimp only at h
  have heq1 : 48 + (idx - 114736) = idx - 114688 := by omega
  have heq2 : 114736 + (idx - 114736) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid2Instr : Nat → Instruction
  | 139314 => .base (.BEQ .x10 .x19 (8#13))
  | 139315 => .base (.JAL .x0 (1998892#21))
  | 139316 => .base (.ADDI .x10 .x10 (96#12))
  | 139317 => .base (.ADDI .x12 .x12 (64#12))
  | 139318 => .base .ECALL
  | 139319 => .base (.LD .x6 .x10 (96#12))
  | 139320 => .base (.SD .x12 .x6 (32#12))
  | 139321 => .base (.LD .x6 .x10 (104#12))
  | 139322 => .base (.SD .x12 .x6 (40#12))
  | 139323 => .base (.LD .x6 .x10 (112#12))
  | 139324 => .base (.SD .x12 .x6 (48#12))
  | 139325 => .base (.LD .x6 .x10 (120#12))
  | 139326 => .base (.SD .x12 .x6 (56#12))
  | 139327 => .base (.ADDI .x24 .x2 (0#12))
  | 139328 => .base (.ADDI .x25 .x2 (128#12))
  | 139329 => .base (.LD .x6 .x24 (0#12))
  | 139330 => .base (.ADD .x10 .x9 .x6)
  | 139331 => .base (.ADDI .x10 .x10 (4000#12))
  | 139332 => .base (.LD .x6 .x24 (8#12))
  | 139333 => .base (.ADD .x12 .x9 .x6)
  | 139334 => .base (.ADDI .x12 .x12 (4032#12))
  | 139335 => .base (.LD .x20 .x24 (16#12))
  | 139336 => .base (.LD .x21 .x24 (24#12))
  | 139337 => .base (.SRLI .x22 .x20 (11#6))
  | 139338 => .base (.BNE .x22 .x0 (8#13))
  | 139339 => .base (.JAL .x0 (32796#21))
  | 139340 => .base (.SLLI .x6 .x22 (16#6))
  | 139341 => .base (.SLLI .x7 .x22 (17#6))
  | 139342 => .base (.ADD .x6 .x6 .x7)
  | 139343 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem get_commitCode_to_commitCode_0_272 (idx : Nat) (hlo : 139264 ≤ idx) (hhi : idx < 139776) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_272.get 32 ⟨idx - 139264, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_34 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279 (idx - 139264) (by omega)
  have hdef : MoonArtifact.commitCode_1_34 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_272 MoonArtifact.commitCode_0_273) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_274 MoonArtifact.commitCode_0_275)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_276 MoonArtifact.commitCode_0_277) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_278 MoonArtifact.commitCode_0_279))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 139264) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  exact packed_get_congr _ (by dsimp only; omega)

private theorem decode_commitMid2Instr_b272 (i : Fin 30) :
    decodeInstruction (MoonArtifact.commitCode_0_272.get 32 ⟨50 + i.val, by omega⟩) =
      some (commitMid2Instr (139314 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid2Instr (state : MachineState) (idx : Nat) (hlo : 139314 ≤ idx) (hhi : idx < 139344)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid2Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_272 idx (by omega) (by omega)]
  have h := decode_commitMid2Instr_b272 ⟨idx - 139314, by omega⟩
  dsimp only at h
  have heq1 : 50 + (idx - 139314) = idx - 139264 := by omega
  have heq2 : 139314 + (idx - 139314) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid3Instr : Nat → Instruction
  | 147536 => .base (.BEQ .x10 .x19 (8#13))
  | 147537 => .base (.JAL .x0 (2064380#21))
  | 147538 => .base (.ANDI .x22 .x20 (2047#12))
  | 147539 => .base (.SRLI .x22 .x22 (1#6))
  | 147540 => .base (.BEQ .x22 .x0 (44#13))
  | 147541 => .base (.ADDI .x10 .x10 (96#12))
  | 147542 => .base (.ADDI .x12 .x12 (64#12))
  | 147543 => .base .ECALL
  | 147544 => .base (.SH .x12 .x0 (30#12))
  | 147545 => .base (.ADDI .x10 .x10 (96#12))
  | 147546 => .base (.ADDI .x12 .x12 (32#12))
  | 147547 => .base .ECALL
  | 147548 => .base (.SH .x12 .x0 (30#12))
  | 147549 => .base (.ADDI .x22 .x22 (4095#12))
  | 147550 => .base (.BNE .x22 .x0 (8156#13))
  | 147551 => .base (.ANDI .x22 .x20 (1#12))
  | 147552 => .base (.BEQ .x22 .x0 (60#13))
  | 147553 => .base (.ADDI .x10 .x10 (96#12))
  | 147554 => .base (.ADDI .x12 .x12 (64#12))
  | 147555 => .base .ECALL
  | 147556 => .base (.SH .x12 .x0 (30#12))
  | 147557 => .base (.BEQ .x21 .x0 (76#13))
  | 147558 => .base (.LD .x6 .x10 (96#12))
  | 147559 => .base (.SD .x12 .x6 (32#12))
  | 147560 => .base (.LD .x6 .x10 (104#12))
  | 147561 => .base (.SD .x12 .x6 (40#12))
  | 147562 => .base (.LD .x6 .x10 (112#12))
  | 147563 => .base (.SD .x12 .x6 (48#12))
  | 147564 => .base (.LD .x6 .x10 (120#12))
  | 147565 => .base (.SD .x12 .x6 (56#12))
  | 147566 => .base (.JAL .x0 (40#21))
  | 147567 => .base (.BEQ .x21 .x0 (36#13))
  | 147568 => .base (.LD .x6 .x10 (96#12))
  | 147569 => .base (.SD .x12 .x6 (64#12))
  | 147570 => .base (.LD .x6 .x10 (104#12))
  | 147571 => .base (.SD .x12 .x6 (72#12))
  | 147572 => .base (.LD .x6 .x10 (112#12))
  | 147573 => .base (.SD .x12 .x6 (80#12))
  | 147574 => .base (.LD .x6 .x10 (120#12))
  | 147575 => .base (.SD .x12 .x6 (88#12))
  | 147576 => .base (.ADDI .x24 .x24 (32#12))
  | 147577 => .base (.BEQ .x24 .x25 (8#13))
  | 147578 => .base (.JAL .x0 (2064156#21))
  | 147579 => .base (.ADDI .x25 .x2 (704#12))
  | 147580 => .base (.ADDI .x27 .x0 (1#12))
  | 147581 => .base (.SLLI .x27 .x27 (46#6))
  | 147582 => .base (.ADDI .x27 .x27 (4095#12))
  | 147583 => .base (.LD .x6 .x24 (0#12))
  | 147584 => .base (.ADD .x10 .x9 .x6)
  | 147585 => .base (.ADDI .x10 .x10 (4000#12))
  | 147586 => .base (.LD .x6 .x24 (8#12))
  | 147587 => .base (.ADD .x12 .x9 .x6)
  | 147588 => .base (.ADDI .x12 .x12 (4032#12))
  | 147589 => .base (.LD .x20 .x24 (16#12))
  | 147590 => .base (.LD .x21 .x24 (24#12))
  | 147591 => .base (.SRLI .x22 .x20 (7#6))
  | 147592 => .base (.BEQ .x22 .x0 (3096#13))
  | 147593 => .base (.SLLI .x6 .x22 (12#6))
  | 147594 => .base (.SLLI .x7 .x22 (13#6))
  | 147595 => .base (.ADD .x6 .x6 .x7)
  | 147596 => .base (.ADD .x19 .x10 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid3Instr_b288 (i : Fin 61) :
    decodeInstruction (MoonArtifact.commitCode_0_288.get 32 ⟨80 + i.val, by omega⟩) =
      some (commitMid3Instr (147536 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid3Instr (state : MachineState) (idx : Nat) (hlo : 147536 ≤ idx) (hhi : idx < 147597)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid3Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_288 idx (by omega) (by omega)]
  have h := decode_commitMid3Instr_b288 ⟨idx - 147536, by omega⟩
  dsimp only at h
  have heq1 : 80 + (idx - 147536) = idx - 147456 := by omega
  have heq2 : 147536 + (idx - 147536) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitTailInstr : Nat → Instruction
  | 148365 => .base (.BNE .x10 .x19 (5120#13))
  | 148366 => .base (.ANDI .x22 .x20 (127#12))
  | 148367 => .base (.SRLI .x22 .x22 (1#6))
  | 148368 => .base (.BEQ .x22 .x0 (60#13))
  | 148369 => .base (.ADDI .x10 .x10 (96#12))
  | 148370 => .base (.ADDI .x12 .x12 (64#12))
  | 148371 => .base .ECALL
  | 148372 => .base (.LD .x6 .x12 (24#12))
  | 148373 => .base (.AND .x6 .x6 .x27)
  | 148374 => .base (.SD .x12 .x6 (24#12))
  | 148375 => .base (.ADDI .x10 .x10 (96#12))
  | 148376 => .base (.ADDI .x12 .x12 (32#12))
  | 148377 => .base .ECALL
  | 148378 => .base (.LD .x6 .x12 (24#12))
  | 148379 => .base (.AND .x6 .x6 .x27)
  | 148380 => .base (.SD .x12 .x6 (24#12))
  | 148381 => .base (.ADDI .x22 .x22 (4095#12))
  | 148382 => .base (.BNE .x22 .x0 (8140#13))
  | 148383 => .base (.ANDI .x22 .x20 (1#12))
  | 148384 => .base (.BEQ .x22 .x0 (68#13))
  | 148385 => .base (.ADDI .x10 .x10 (96#12))
  | 148386 => .base (.ADDI .x12 .x12 (64#12))
  | 148387 => .base .ECALL
  | 148388 => .base (.LD .x6 .x12 (24#12))
  | 148389 => .base (.AND .x6 .x6 .x27)
  | 148390 => .base (.SD .x12 .x6 (24#12))
  | 148391 => .base (.BEQ .x21 .x0 (76#13))
  | 148392 => .base (.LD .x6 .x10 (96#12))
  | 148393 => .base (.SD .x12 .x6 (32#12))
  | 148394 => .base (.LD .x6 .x10 (104#12))
  | 148395 => .base (.SD .x12 .x6 (40#12))
  | 148396 => .base (.LD .x6 .x10 (112#12))
  | 148397 => .base (.SD .x12 .x6 (48#12))
  | 148398 => .base (.LD .x6 .x10 (120#12))
  | 148399 => .base (.SD .x12 .x6 (56#12))
  | 148400 => .base (.JAL .x0 (40#21))
  | 148401 => .base (.BEQ .x21 .x0 (36#13))
  | 148402 => .base (.LD .x6 .x10 (96#12))
  | 148403 => .base (.SD .x12 .x6 (64#12))
  | 148404 => .base (.LD .x6 .x10 (104#12))
  | 148405 => .base (.SD .x12 .x6 (72#12))
  | 148406 => .base (.LD .x6 .x10 (112#12))
  | 148407 => .base (.SD .x12 .x6 (80#12))
  | 148408 => .base (.LD .x6 .x10 (120#12))
  | 148409 => .base (.SD .x12 .x6 (88#12))
  | 148410 => .base (.ADDI .x24 .x24 (32#12))
  | 148411 => .base (.BNE .x24 .x25 (4880#13))
  | 148412 => .base (.ADDI .x6 .x0 (256#12))
  | 148413 => .base (.SLLI .x6 .x6 (11#6))
  | 148414 => .base (.SLLI .x6 .x6 (11#6))
  | 148415 => .base (.ADDI .x6 .x6 (928#12))
  | 148416 => .base (.ADD .x10 .x9 .x6)
  | 148417 => .base (.ADDI .x6 .x0 (256#12))
  | 148418 => .base (.SLLI .x6 .x6 (11#6))
  | 148419 => .base (.SLLI .x6 .x6 (11#6))
  | 148420 => .base (.ADDI .x6 .x6 (1024#12))
  | 148421 => .base (.ADD .x12 .x9 .x6)
  | 148422 => .base .ECALL
  | 148423 => .base (.LD .x6 .x12 (0#12))
  | 148424 => .base (.SD .x26 .x6 (0#12))
  | 148425 => .base (.LD .x6 .x12 (8#12))
  | 148426 => .base (.SD .x26 .x6 (8#12))
  | 148427 => .base (.LD .x6 .x12 (16#12))
  | 148428 => .base (.SD .x26 .x6 (16#12))
  | 148429 => .base (.LD .x6 .x12 (24#12))
  | 148430 => .base (.SD .x26 .x6 (24#12))
  | 148431 => .base (.ADDI .x5 .x0 (1#12))
  | 148432 => .base (.ADDI .x10 .x0 (0#12))
  | 148433 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr_b289 (i : Fin 69) :
    decodeInstruction (MoonArtifact.commitCode_0_289.get 32 ⟨397 + i.val, by omega⟩) =
      some (commitTailInstr (148365 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 148365 ≤ idx) (hhi : idx < 148434)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_289 idx (by omega) (by omega)]
  have h := decode_commitTailInstr_b289 ⟨idx - 148365, by omega⟩
  dsimp only at h
  have heq1 : 397 + (idx - 148365) = idx - 147968 := by omega
  have heq2 : 148365 + (idx - 148365) = idx := by omega
  simp only [heq1, heq2] at h; exact h

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
