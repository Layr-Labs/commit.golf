import CommitGolfCandidate.MoonArtifact
import CommitGolfCandidate.MoonTree
import CommitGolf.Statements

/-! Fast instruction-fetch and admission proofs for the packed submission images.
Uses O(1) periodic block deduplication on `ArtifactEncoding.Packed` so large unrolls
compile fast at low RAM without O(N) `decide`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def submission : CommitGolf.Submission := MoonArtifact.submission

theorem submission_sizes :
    submission.sizes = ⟨2080374784, 8480886496⟩ := rfl

theorem submission_layout :
    submission.layout = ⟨4096, 4294971392, 4294971424, 6375346208, 6509563936, 10804531232⟩ := rfl

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
  · rw [pick8_0, ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_1, ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_2, ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_3, ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_4, ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_5, ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_6, ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)
  · rw [pick8_7, ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    exact packed_get_congr _ (by dsimp only; omega)

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
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_2_1 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 43887) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_2_1.get 32 ⟨idx - 32768, by omega⟩ := by
  unfold MoonArtifact.commitCode
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 4096) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_0.get 32 ⟨idx - 0, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_1 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 8192) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_1.get 32 ⟨idx - 4096, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_2 (idx : Nat) (hlo : 8192 ≤ idx) (hhi : idx < 12288) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_2.get 32 ⟨idx - 8192, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_3 (idx : Nat) (hlo : 12288 ≤ idx) (hhi : idx < 16384) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_3.get 32 ⟨idx - 12288, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_4 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 20480) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_4.get 32 ⟨idx - 16384, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_5 (idx : Nat) (hlo : 20480 ≤ idx) (hhi : idx < 24576) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_5.get 32 ⟨idx - 20480, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_6 (idx : Nat) (hlo : 24576 ≤ idx) (hhi : idx < 28672) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_6.get 32 ⟨idx - 24576, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_7 (idx : Nat) (hlo : 28672 ≤ idx) (hhi : idx < 32768) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_7.get 32 ⟨idx - 28672, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 4096) MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_2_0 = (@ArtifactEncoding.Packed.join 16384 16384 (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_0 MoonArtifact.commitCode_1_1) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_2 MoonArtifact.commitCode_1_3)) (@ArtifactEncoding.Packed.join 8192 8192 (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_4 MoonArtifact.commitCode_1_5) (@ArtifactEncoding.Packed.join 4096 4096 MoonArtifact.commitCode_1_6 MoonArtifact.commitCode_1_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 4096 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_8 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 36864) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_8.get 32 ⟨idx - 32768, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_9 (idx : Nat) (hlo : 36864 ≤ idx) (hhi : idx < 40960) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_9.get 32 ⟨idx - 36864, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_1_10 (idx : Nat) (hlo : 40960 ≤ idx) (hhi : idx < 43887) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_1_10.get 32 ⟨idx - 40960, by omega⟩ := by
  rw [get_commitCode_to_commitCode_2_1 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_2_1
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

/-! ### Commit Program: Periodic Unrolled Loops -/

def p0Word : Nat → BitVec 32
  | 0 => (115#32)
  | 1 => (126158099#32)
  | _ => 0#32

def p0Instr : Nat → Instruction
  | 0 => .base .ECALL
  | 1 => .base (.ADDI .x10 .x10 (120#12))
  | _ => .base .EBREAK

private theorem decode_p0Word (j : Fin 2) :
    decodeInstruction (p0Word j.val) = some (p0Instr j.val) := by
  revert j; decide

private abbrev p0_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 949262653321040790611668476324317921123906793421212848329801007829722224499173602782822772478984749064020205364369145848641070715667079070586858828439334849302700397448052487686559620806459001898069357441366205665984166644020877846127199684925012234558409267957210393284390268006640752900033086879408967130826447708669881137137728517209842509910466645353354052408873832400124569090574804519182531526034872913364330370715099719885270133517263833714640373548634601183843576921384639338736098465036918104189269402408307687329206996113715396674859140200545543957456003119419868963146496523546756462833844636244852605043

private theorem p0_chunk64_p0 (i : Fin 64) :
    p0_c64_p0.get 32 i =
      p0Word ((i.val + 0) % 2) := by
  revert i; decide

private theorem get_commitCode_to_commitCode_0_0 (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 512) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_0.get 32 ⟨idx - 0, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem p0_bnd64_0 (i : Fin 50) :
    (ArtifactEncoding.Packed.chunk 64 949262653321040790611668476324317921123906793421212848329801007829722224499173602782822772478984749064020205364369145848641070715667079070586858828439334849302700397448052487686559620806459001898069357441366205665984166644020877846127199684925012234558409267957210393284390268006640752900033086879408967130826447708669881137137728517209842509910466645353354052408873832400124569090574804519182531526034872913364330370715099719885270133517263833714640373548634601183843576921384639318551263462206163274678087773566280252005863124546250797869938279924283267999672347421023999060172608326552211436890925084563906823187).get 32 ⟨14 + i.val, by omega⟩ =
      p0Word ((0 + i.val) % 2) := by
  revert i; decide

private theorem p0_blk512_0 (r : Nat) (hlo : 14 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_0.get 32 ⟨r, by omega⟩ = p0Word ((0 + r - 14) % 2) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p0_bnd64_0 ⟨r - 0 - 14, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 0 - 14)) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_0
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p0_chunk64_p0 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 0) % 2 = (0 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_1 (idx : Nat) (hlo : 512 ≤ idx) (hhi : idx < 1024) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_1.get 32 ⟨idx - 512, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev p0_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p0_c64_p0 p0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 p0_c64_p0 p0_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p0_c64_p0 p0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 p0_c64_p0 p0_c64_p0))

private theorem p0_eval512_p0 (r : Nat) (hhi : r < 512) :
    p0_pat512_p0.get 32 ⟨r, hhi⟩ = p0Word ((r + 0) % 2) := by
  have h8 := packed_get_join8 (S := 64) p0_c64_p0 p0_c64_p0 p0_c64_p0 p0_c64_p0 p0_c64_p0 p0_c64_p0 p0_c64_p0 p0_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, p0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_2 (idx : Nat) (hlo : 1024 ≤ idx) (hhi : idx < 1536) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_2.get 32 ⟨idx - 1024, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_3 (idx : Nat) (hlo : 1536 ≤ idx) (hhi : idx < 2048) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_3.get 32 ⟨idx - 1536, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_4 (idx : Nat) (hlo : 2048 ≤ idx) (hhi : idx < 2560) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_4.get 32 ⟨idx - 2048, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_5 (idx : Nat) (hlo : 2560 ≤ idx) (hhi : idx < 3072) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_5.get 32 ⟨idx - 2560, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_6 (idx : Nat) (hlo : 3072 ≤ idx) (hhi : idx < 3584) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_6.get 32 ⟨idx - 3072, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_7 (idx : Nat) (hlo : 3584 ≤ idx) (hhi : idx < 4096) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_7.get 32 ⟨idx - 3584, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_0 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7 (idx - 0) (by omega)
  have hdef : MoonArtifact.commitCode_1_0 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_0 MoonArtifact.commitCode_0_1) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_2 MoonArtifact.commitCode_0_3)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_4 MoonArtifact.commitCode_0_5) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_6 MoonArtifact.commitCode_0_7))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 0) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_8 (idx : Nat) (hlo : 4096 ≤ idx) (hhi : idx < 4608) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_8.get 32 ⟨idx - 4096, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem p0_bnd64_64 (i : Fin 14) :
    (ArtifactEncoding.Packed.chunk 64 2477292790118680573345614194051835400344423991655269795898565061589709544687332178265748075965485018778107090596107478060494679298705169745165271725337758060482647707324774849556671966330879951564859038873141487332566652298237940388009896282104458690978952479448020303687025194123634044486200495766965570062984037356510288218904188235080300184131477526548973858177302327720992794839842658728861998405423563609416889899290262103404343572273862816670394092739940078417905688352493015358926179166971203212437903328793963727097928151184574125982368699498562452547582054117074960317896850131589106116024545765266292851).get 32 ⟨0 + i.val, by omega⟩ =
      p0Word ((0 + i.val) % 2) := by
  revert i; decide

private theorem p0_blk512_8 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 14) :
    MoonArtifact.commitCode_0_8.get 32 ⟨r, by omega⟩ = p0Word ((4096 + r - 14) % 2) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p0_bnd64_64 ⟨r - 0 - 0, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 0 - 0)) % 2 = (4096 + r - 14) % 2 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_p0 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 2)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k + j))) :
    fetch (submission.image .commit) state = some (p0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (14 + 2 * k + j) (by omega)
    (p0Word j) hpc _ (p0Instr j) (decode_p0Word ⟨j, hj⟩)
  have hb_lo : 0 ≤ (14 + 2 * k + j) / 512 := by omega
  have hb_hi : (14 + 2 * k + j) / 512 ≤ 8 := by omega
  generalize hbv : (14 + 2 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_0 (14 + 2 * k + j) (by omega) (by omega)]
    rw [p0_blk512_0 (14 + 2 * k + j - 0) (by omega) (by omega)]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_1 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_1 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_2 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_2 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_3 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_3 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_4 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_4 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_5 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_5 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_6 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_6 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_7 (14 + 2 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_7 = p0_pat512_p0 := rfl
    rw [hpat, p0_eval512_p0]
    exact congrArg p0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_8 (14 + 2 * k + j) (by omega) (by omega)]
    rw [p0_blk512_8 (14 + 2 * k + j - 4096) (by omega) (by omega)]
    exact congrArg p0Word (by omega)

def c0Word : Nat → BitVec 32
  | 0 => (268764435#32)
  | 1 => (329235#32)
  | 2 => (115#32)
  | _ => 0#32

def c0Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (256#12))
  | 1 => .base (.ADDI .x12 .x10 (0#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_c0Word (j : Fin 3) :
    decodeInstruction (c0Word j.val) = some (c0Instr j.val) := by
  revert j; decide

private abbrev c0_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865305349112850604174375572430723935199545731637923121211301913189328492311609941546306113729535372417704515069049985229340803296534753085836973667543678986055453163545420829981128288890881539127206940500346627899752566057851903651969453519867044340021810553021881386626599103806637388566488635749497395311619669972883820507830705261939009784769416874167521853384749458190444959485706523213634813381903793252706610302652462922491100442171500392052750359356606766694791177161512258126589101419753498432844730831701307329414305145866297133396205533648048552997442428063695234023038329185722392179562488644239475

private theorem c0_chunk64_p2 (i : Fin 64) :
    c0_c64_p2.get 32 i =
      c0Word ((i.val + 2) % 3) := by
  revert i; decide

private abbrev c0_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2022288245532539079841891779139557554037653383294122497596024948429925972192918049376523935366212360777031869668722715704113035040794872148324326864930512454968425944181141849837641605395492133558236756895032562361256332276972957290066462438148655622951472186445484670379637536800243532738492536340101205635062706523870853359753243263187068501023696152820439021565064972171503844997600802801893148925518339535126151609944541209464850010546593298708918963659527948741762001982903673044531726102375972090575800482605600774802532013540101813585709523379353692676130517815020501697482648303861165267789386063607251666195

private theorem c0_chunk64_p0 (i : Fin 64) :
    c0_c64_p0.get 32 i =
      c0Word ((i.val + 0) % 3) := by
  revert i; decide

private abbrev c0_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2477292790118680573345614194051835400344423991655269795898565061589709544687332178265748075965485018778107090596107478060494679298705169745165271725337758060482647707324774849556671966330879951564859038873141487332566652298237940388009896282104458690978952479448020303687025194123634044486200495766965570062984037356510288218904188235080300184131477526548973858177258612428517681560529146606582959581815236840305285876709828048867663044128111315874767045632895310665716292934438417351929271341951642338771304474757749249750199660933160466783377810815756623754601582230505804509367590487503848125150108070351013395

private theorem c0_chunk64_p1 (i : Fin 64) :
    c0_c64_p1.get 32 i =
      c0Word ((i.val + 1) % 3) := by
  revert i; decide

private theorem c0_bnd64_64 (i : Fin 38) :
    (ArtifactEncoding.Packed.chunk 64 2477292790118680573345614194051835400344423991655269795898565061589709544687332178265748075965485018778107090596107478060494679298705169745165271725337758060482647707324774849556671966330879951564859038873141487332566652298237940388009896282104458690978952479448020303687025194123634044486200495766965570062984037356510288218904188235080300184131477526548973858177302327720992794839842658728861998405423563609416889899290262103404343572273862816670394092739940078417905688352493015358926179166971203212437903328793963727097928151184574125982368699498562452547582054117074960317896850131589106116024545765266292851).get 32 ⟨26 + i.val, by omega⟩ =
      c0Word ((0 + i.val) % 3) := by
  revert i; decide

private theorem c0_blk512_8 (r : Nat) (hlo : 26 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_8.get 32 ⟨r, by omega⟩ = c0Word ((4096 + r - 4122) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c0_bnd64_64 ⟨r - 0 - 26, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 0 - 26)) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p2 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 2) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p0 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 0) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p1 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 1) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p2 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 2) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p0 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 0) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p1 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 1) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_8
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c0_chunk64_p2 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 2) % 3 = (4096 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_9 (idx : Nat) (hlo : 4608 ≤ idx) (hhi : idx < 5120) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_9.get 32 ⟨idx - 4608, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c0_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p0 c0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p2 c0_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p1 c0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p0 c0_c64_p1))

private theorem c0_eval512_p0 (r : Nat) (hhi : r < 512) :
    c0_pat512_p0.get 32 ⟨r, hhi⟩ = c0Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) c0_c64_p0 c0_c64_p1 c0_c64_p2 c0_c64_p0 c0_c64_p1 c0_c64_p2 c0_c64_p0 c0_c64_p1 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_10 (idx : Nat) (hlo : 5120 ≤ idx) (hhi : idx < 5632) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_10.get 32 ⟨idx - 5120, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c0_pat512_p2 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p2 c0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p1 c0_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p0 c0_c64_p1) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p2 c0_c64_p0))

private theorem c0_eval512_p2 (r : Nat) (hhi : r < 512) :
    c0_pat512_p2.get 32 ⟨r, hhi⟩ = c0Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) c0_c64_p2 c0_c64_p0 c0_c64_p1 c0_c64_p2 c0_c64_p0 c0_c64_p1 c0_c64_p2 c0_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_11 (idx : Nat) (hlo : 5632 ≤ idx) (hhi : idx < 6144) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_11.get 32 ⟨idx - 5632, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c0_pat512_p1 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p1 c0_c64_p2) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p0 c0_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c0_c64_p2 c0_c64_p0) (@ArtifactEncoding.Packed.join 64 64 c0_c64_p1 c0_c64_p2))

private theorem c0_eval512_p1 (r : Nat) (hhi : r < 512) :
    c0_pat512_p1.get 32 ⟨r, hhi⟩ = c0Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) c0_c64_p1 c0_c64_p2 c0_c64_p0 c0_c64_p1 c0_c64_p2 c0_c64_p0 c0_c64_p1 c0_c64_p2 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c0_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c0_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c0_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_12 (idx : Nat) (hlo : 6144 ≤ idx) (hhi : idx < 6656) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_12.get 32 ⟨idx - 6144, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_13 (idx : Nat) (hlo : 6656 ≤ idx) (hhi : idx < 7168) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_13.get 32 ⟨idx - 6656, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_14 (idx : Nat) (hlo : 7168 ≤ idx) (hhi : idx < 7680) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_14.get 32 ⟨idx - 7168, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_15 (idx : Nat) (hlo : 7680 ≤ idx) (hhi : idx < 8192) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_15.get 32 ⟨idx - 7680, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_1 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15 (idx - 4096) (by omega)
  have hdef : MoonArtifact.commitCode_1_1 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_8 MoonArtifact.commitCode_0_9) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_10 MoonArtifact.commitCode_0_11)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_12 MoonArtifact.commitCode_0_13) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_14 MoonArtifact.commitCode_0_15))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 4096) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_16 (idx : Nat) (hlo : 8192 ≤ idx) (hhi : idx < 8704) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_16.get 32 ⟨idx - 8192, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_17 (idx : Nat) (hlo : 8704 ≤ idx) (hhi : idx < 9216) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_17.get 32 ⟨idx - 8704, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_18 (idx : Nat) (hlo : 9216 ≤ idx) (hhi : idx < 9728) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_18.get 32 ⟨idx - 9216, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_19 (idx : Nat) (hlo : 9728 ≤ idx) (hhi : idx < 10240) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_19.get 32 ⟨idx - 9728, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_20 (idx : Nat) (hlo : 10240 ≤ idx) (hhi : idx < 10752) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_20.get 32 ⟨idx - 10240, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem c0_bnd64_160 (i : Fin 26) :
    (ArtifactEncoding.Packed.chunk 64 865305349112850604174375572430723935199545731637923121211301913189328492311609941546306113729535372417704515069049985229340803296534753085836973667543678986055453163545420829981128288890881539127206940500346627899752566057851903651969453519867044340021810954065730034699329379972060242023650256652138516911009071223072855432737105063961090562758591267608701105026732941603986695510050424542655374356120609180607250553303371499221652651711909287636440551824291898527259505949878096685779458828689619290654921169959002204148554624330509950266082873075112125498316390822075961373702105080387457411846143452972563).get 32 ⟨0 + i.val, by omega⟩ =
      c0Word ((1 + i.val) % 3) := by
  revert i; decide

private theorem c0_blk512_20 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 26) :
    MoonArtifact.commitCode_0_20.get 32 ⟨r, by omega⟩ = c0Word ((10240 + r - 4122) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c0_bnd64_160 ⟨r - 0 - 0, by omega⟩
    dsimp only at h
    have heq2 : (1 + (r - 0 - 0)) % 3 = (10240 + r - 4122) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_c0 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (c0Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (4122 + 3 * k + j) (by omega)
    (c0Word j) hpc _ (c0Instr j) (decode_c0Word ⟨j, hj⟩)
  have hb_lo : 8 ≤ (4122 + 3 * k + j) / 512 := by omega
  have hb_hi : (4122 + 3 * k + j) / 512 ≤ 20 := by omega
  generalize hbv : (4122 + 3 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_8 (4122 + 3 * k + j) (by omega) (by omega)]
    rw [c0_blk512_8 (4122 + 3 * k + j - 4096) (by omega) (by omega)]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_9 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_9 = c0_pat512_p0 := rfl
    rw [hpat, c0_eval512_p0]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_10 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_10 = c0_pat512_p2 := rfl
    rw [hpat, c0_eval512_p2]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_11 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_11 = c0_pat512_p1 := rfl
    rw [hpat, c0_eval512_p1]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_12 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_12 = c0_pat512_p0 := rfl
    rw [hpat, c0_eval512_p0]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_13 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_13 = c0_pat512_p2 := rfl
    rw [hpat, c0_eval512_p2]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_14 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_14 = c0_pat512_p1 := rfl
    rw [hpat, c0_eval512_p1]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_15 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_15 = c0_pat512_p0 := rfl
    rw [hpat, c0_eval512_p0]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_16 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_16 = c0_pat512_p2 := rfl
    rw [hpat, c0_eval512_p2]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_17 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_17 = c0_pat512_p1 := rfl
    rw [hpat, c0_eval512_p1]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_18 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_18 = c0_pat512_p0 := rfl
    rw [hpat, c0_eval512_p0]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_19 (4122 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_19 = c0_pat512_p2 := rfl
    rw [hpat, c0_eval512_p2]
    exact congrArg c0Word (by omega)
  · rw [get_commitCode_to_commitCode_0_20 (4122 + 3 * k + j) (by omega) (by omega)]
    rw [c0_blk512_20 (4122 + 3 * k + j - 10240) (by omega) (by omega)]
    exact congrArg c0Word (by omega)

def p1Word : Nat → BitVec 32
  | 0 => (268764435#32)
  | 1 => (329235#32)
  | 2 => (115#32)
  | _ => 0#32

def p1Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (256#12))
  | 1 => .base (.ADDI .x12 .x10 (0#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_p1Word (j : Fin 3) :
    decodeInstruction (p1Word j.val) = some (p1Instr j.val) := by
  revert j; decide

private abbrev p1_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2022288245532539079841891779139557554037653383294122497596024948429925972192918049376523935366212360777031869668722715704113035040794872148324326864930512454968425944181141849837641605395492133558236756895032562361256332276972957290066462438148655622951472186445484670379637536800243532738492536340101205635062706523870853359753243263187068501023696152820439021565064972171503844997600802801893148925518339535126151609944541209464850010546593298708918963659527948741762001982903673044531726102375972090575800482605600774802532013540101813585709523379353692676130517815020501697482648303861165267789386063607251666195

private theorem p1_chunk64_p0 (i : Fin 64) :
    p1_c64_p0.get 32 i =
      p1Word ((i.val + 0) % 3) := by
  revert i; decide

private abbrev p1_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2477292790118680573345614194051835400344423991655269795898565061589709544687332178265748075965485018778107090596107478060494679298705169745165271725337758060482647707324774849556671966330879951564859038873141487332566652298237940388009896282104458690978952479448020303687025194123634044486200495766965570062984037356510288218904188235080300184131477526548973858177258612428517681560529146606582959581815236840305285876709828048867663044128111315874767045632895310665716292934438417351929271341951642338771304474757749249750199660933160466783377810815756623754601582230505804509367590487503848125150108070351013395

private theorem p1_chunk64_p1 (i : Fin 64) :
    p1_c64_p1.get 32 i =
      p1Word ((i.val + 1) % 3) := by
  revert i; decide

private abbrev p1_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865305349112850604174375572430723935199545731637923121211301913189328492311609941546306113729535372417704515069049985229340803296534753085836973667543678986055453163545420829981128288890881539127206940500346627899752566057851903651969453519867044340021810553021881386626599103806637388566488635749497395311619669972883820507830705261939009784769416874167521853384749458190444959485706523213634813381903793252706610302652462922491100442171500392052750359356606766694791177161512258126589101419753498432844730831701307329414305145866297133396205533648048552997442428063695234023038329185722392179562488644239475

private theorem p1_chunk64_p2 (i : Fin 64) :
    p1_c64_p2.get 32 i =
      p1Word ((i.val + 2) % 3) := by
  revert i; decide

private theorem p1_bnd64_160 (i : Fin 27) :
    (ArtifactEncoding.Packed.chunk 64 865305349112850604174375572430723935199545731637923121211301913189328492311609941546306113729535372417704515069049985229340803296534753085836973667543678986055453163545420829981128288890881539127206940500346627899752566057851903651969453519867044340021810954065730034699329379972060242023650256652138516911009071223072855432737105063961090562758591267608701105026732941603986695510050424542655374356120609180607250553303371499221652651711909287636440551824291898527259505949878096685779458828689619290654921169959002204148554624330509950266082873075112125498316390822075961373702105080387457411846143452972563).get 32 ⟨37 + i.val, by omega⟩ =
      p1Word ((0 + i.val) % 3) := by
  revert i; decide

private theorem p1_blk512_20 (r : Nat) (hlo : 37 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_20.get 32 ⟨r, by omega⟩ = p1Word ((10240 + r - 10277) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p1_bnd64_160 ⟨r - 0 - 37, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 0 - 37)) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p0 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 0) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p1 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 1) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p2 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 2) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p0 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 0) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p1 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 1) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p2 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 2) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_20
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := p1_chunk64_p0 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 0) % 3 = (10240 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_21 (idx : Nat) (hlo : 10752 ≤ idx) (hhi : idx < 11264) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_21.get 32 ⟨idx - 10752, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev p1_pat512_p1 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p1 p1_c64_p2) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p0 p1_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p2 p1_c64_p0) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p1 p1_c64_p2))

private theorem p1_eval512_p1 (r : Nat) (hhi : r < 512) :
    p1_pat512_p1.get 32 ⟨r, hhi⟩ = p1Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) p1_c64_p1 p1_c64_p2 p1_c64_p0 p1_c64_p1 p1_c64_p2 p1_c64_p0 p1_c64_p1 p1_c64_p2 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_22 (idx : Nat) (hlo : 11264 ≤ idx) (hhi : idx < 11776) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_22.get 32 ⟨idx - 11264, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev p1_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p0 p1_c64_p1) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p2 p1_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p1 p1_c64_p2) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p0 p1_c64_p1))

private theorem p1_eval512_p0 (r : Nat) (hhi : r < 512) :
    p1_pat512_p0.get 32 ⟨r, hhi⟩ = p1Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) p1_c64_p0 p1_c64_p1 p1_c64_p2 p1_c64_p0 p1_c64_p1 p1_c64_p2 p1_c64_p0 p1_c64_p1 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_23 (idx : Nat) (hlo : 11776 ≤ idx) (hhi : idx < 12288) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_23.get 32 ⟨idx - 11776, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_2 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23 (idx - 8192) (by omega)
  have hdef : MoonArtifact.commitCode_1_2 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_16 MoonArtifact.commitCode_0_17) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_18 MoonArtifact.commitCode_0_19)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_20 MoonArtifact.commitCode_0_21) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_22 MoonArtifact.commitCode_0_23))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 8192) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev p1_pat512_p2 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p2 p1_c64_p0) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p1 p1_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 p1_c64_p0 p1_c64_p1) (@ArtifactEncoding.Packed.join 64 64 p1_c64_p2 p1_c64_p0))

private theorem p1_eval512_p2 (r : Nat) (hhi : r < 512) :
    p1_pat512_p2.get 32 ⟨r, hhi⟩ = p1Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) p1_c64_p2 p1_c64_p0 p1_c64_p1 p1_c64_p2 p1_c64_p0 p1_c64_p1 p1_c64_p2 p1_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, p1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, p1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, p1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_24 (idx : Nat) (hlo : 12288 ≤ idx) (hhi : idx < 12800) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_24.get 32 ⟨idx - 12288, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_25 (idx : Nat) (hlo : 12800 ≤ idx) (hhi : idx < 13312) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_25.get 32 ⟨idx - 12800, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_26 (idx : Nat) (hlo : 13312 ≤ idx) (hhi : idx < 13824) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_26.get 32 ⟨idx - 13312, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_27 (idx : Nat) (hlo : 13824 ≤ idx) (hhi : idx < 14336) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_27.get 32 ⟨idx - 13824, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_28 (idx : Nat) (hlo : 14336 ≤ idx) (hhi : idx < 14848) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_28.get 32 ⟨idx - 14336, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_29 (idx : Nat) (hlo : 14848 ≤ idx) (hhi : idx < 15360) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_29.get 32 ⟨idx - 14848, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_30 (idx : Nat) (hlo : 15360 ≤ idx) (hhi : idx < 15872) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_30.get 32 ⟨idx - 15360, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_31 (idx : Nat) (hlo : 15872 ≤ idx) (hhi : idx < 16384) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_31.get 32 ⟨idx - 15872, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_3 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31 (idx - 12288) (by omega)
  have hdef : MoonArtifact.commitCode_1_3 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_24 MoonArtifact.commitCode_0_25) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_26 MoonArtifact.commitCode_0_27)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_28 MoonArtifact.commitCode_0_29) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_30 MoonArtifact.commitCode_0_31))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 12288) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_32 (idx : Nat) (hlo : 16384 ≤ idx) (hhi : idx < 16896) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_32.get 32 ⟨idx - 16384, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem p1_bnd64_256 (i : Fin 37) :
    (ArtifactEncoding.Packed.chunk 64 865364248217518173431468716773946392130167991390475090413238700759683926141311963483050921087133455334533274499900817501731487529828495451748034866146766905962406022991914142576720266252856623057496845426787367629239764347393665932914365793616265898212252641680324008546400556838540927431105796988590799604800212440778786583067258320451378448187520182273273714870261736987210951453175712032156939565279754401448165508106701526185991436832238787220868616150411331914370069438238247287668722663652728001468963814642472991194575914264239231139763902586887003784913491351346976000225476950114787001443337421979763).get 32 ⟨0 + i.val, by omega⟩ =
      p1Word ((2 + i.val) % 3) := by
  revert i; decide

private theorem p1_blk512_32 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 37) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = p1Word ((16384 + r - 10277) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := p1_bnd64_256 ⟨r - 0 - 0, by omega⟩
    dsimp only at h
    have heq2 : (2 + (r - 0 - 0)) % 3 = (16384 + r - 10277) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_p1 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (p1Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (10277 + 3 * k + j) (by omega)
    (p1Word j) hpc _ (p1Instr j) (decode_p1Word ⟨j, hj⟩)
  have hb_lo : 20 ≤ (10277 + 3 * k + j) / 512 := by omega
  have hb_hi : (10277 + 3 * k + j) / 512 ≤ 32 := by omega
  generalize hbv : (10277 + 3 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_20 (10277 + 3 * k + j) (by omega) (by omega)]
    rw [p1_blk512_20 (10277 + 3 * k + j - 10240) (by omega) (by omega)]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_21 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_21 = p1_pat512_p1 := rfl
    rw [hpat, p1_eval512_p1]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_22 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_22 = p1_pat512_p0 := rfl
    rw [hpat, p1_eval512_p0]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_23 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_23 = p1_pat512_p2 := rfl
    rw [hpat, p1_eval512_p2]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_24 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_24 = p1_pat512_p1 := rfl
    rw [hpat, p1_eval512_p1]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_25 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_25 = p1_pat512_p0 := rfl
    rw [hpat, p1_eval512_p0]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_26 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_26 = p1_pat512_p2 := rfl
    rw [hpat, p1_eval512_p2]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_27 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_27 = p1_pat512_p1 := rfl
    rw [hpat, p1_eval512_p1]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_28 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_28 = p1_pat512_p0 := rfl
    rw [hpat, p1_eval512_p0]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_29 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_29 = p1_pat512_p2 := rfl
    rw [hpat, p1_eval512_p2]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_30 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_30 = p1_pat512_p1 := rfl
    rw [hpat, p1_eval512_p1]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_31 (10277 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_31 = p1_pat512_p0 := rfl
    rw [hpat, p1_eval512_p0]
    exact congrArg p1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_32 (10277 + 3 * k + j) (by omega) (by omega)]
    rw [p1_blk512_32 (10277 + 3 * k + j - 16384) (by omega) (by omega)]
    exact congrArg p1Word (by omega)

def c2PairWord : Nat → BitVec 32
  | 0 => (268764435#32)
  | 1 => (33949203#32)
  | 2 => (115#32)
  | 3 => (268764435#32)
  | 4 => (92669459#32)
  | 5 => (115#32)
  | _ => 0#32

def c2PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (256#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (256#12))
  | 4 => .base (.ADDI .x12 .x12 (88#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_c2PairWord (j : Fin 6) :
    decodeInstruction (c2PairWord j.val) = some (c2PairInstr j.val) := by
  revert j; decide

private abbrev c2Pair_c64_p3 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 2022288245532539079879557168376584811361013034330375417824347175244028210145531221215524155816108100098095825029491254682952860235954594278039573511817932911650731562818020574838412260763488229598721011476159155026807731525974858978243724803346069969424774283743194422949115125134057172627718655204608692438116376297258138021292893185360438876078345731341124869869960322562249206056658398844742056815274164276191220370266345666883154324461343224182165659456159327907310107989338053849595556490758645148031015488479455039580681662504728283302738288956666921820362199244781876713067521333655134462504631836910803027219

private theorem c2Pair_chunk64_p3 (i : Fin 64) :
    c2Pair_c64_p3.get 32 i =
      c2PairWord ((i.val + 3) % 6) := by
  revert i; decide

private abbrev c2Pair_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 697281088482214769542877798864236374693058602341582525568966022072890743875743253211635079547934780517146304760159567735095254155752767255445990241400166667997922671569548813133239067837767755128104181338671365487635661090788907116801371320908816557370065363817191702494865525541013059922561573994103517156320633919150513183044437533690042777050508412325358553607232573765437652040715374443086795111821020284423844303091115456967654964652893776072925179759425399432506719194702222531087538438203141641846118787141839631073948006668835216781497784041558453633709514909730231301712537471077512845230409845575963248147

private theorem c2Pair_chunk64_p1 (i : Fin 64) :
    c2Pair_c64_p1.get 32 i =
      c2PairWord ((i.val + 1) % 6) := by
  revert i; decide

private abbrev c2Pair_c64_p5 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217518173431468716773946392130167991390475090413238700759683926141311963483050921087133455334533274499900817501731487529828495451732232934003253413431620965224475890495550194260391605321639943709272439972372300645197979380709511999489836452373480934461461562448876166552190439044952035304863624169859448553878745651840917157305205457294971143560526341795432537436796705236914128332988364087675515420637516161331553342213447537849987815697508959538195394923400590868890496606139582426470811567561849239717546004171906975411423358471122287933146468892178229847385993989608887702467519371272865257095283

private theorem c2Pair_chunk64_p5 (i : Fin 64) :
    c2Pair_c64_p5.get 32 i =
      c2PairWord ((i.val + 5) % 6) := by
  revert i; decide

private theorem c2Pair_bnd64_256 (i : Fin 15) :
    (ArtifactEncoding.Packed.chunk 64 865364248217518173431468716773946392130167991390475090413238700759683926141311963483050921087133455334533274499900817501731487529828495451748034866146766905962406022991914142576720266252856623057496845426787367629239764347393665932914365793616265898212252641680324008546400556838540927431105796988590799604800212440778786583067258320451378448187520182273273714870261736987210951453175712032156939565279754401448165508106701526185991436832238787220868616150411331914370069438238247287668722663652728001468963814642472991194575914264239231139763902586887003784913491351346976000225476950114787001443337421979763).get 32 ⟨49 + i.val, by omega⟩ =
      c2PairWord ((0 + i.val) % 6) := by
  revert i; decide

private theorem c2Pair_blk512_32 (r : Nat) (hlo : 49 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_32.get 32 ⟨r, by omega⟩ = c2PairWord ((16384 + r - 16433) % 6) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_bnd64_256 ⟨r - 0 - 49, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 0 - 49)) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p3 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 3) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p1 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 1) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p5 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 5) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p3 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 3) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p1 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 1) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p5 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 5) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_32
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_chunk64_p3 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 3) % 6 = (16384 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_33 (idx : Nat) (hlo : 16896 ≤ idx) (hhi : idx < 17408) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_33.get 32 ⟨idx - 16896, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c2Pair_pat512_p1 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p1 c2Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p3 c2Pair_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p5 c2Pair_c64_p3) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p1 c2Pair_c64_p5))

private theorem c2Pair_eval512_p1 (r : Nat) (hhi : r < 512) :
    c2Pair_pat512_p1.get 32 ⟨r, hhi⟩ = c2PairWord ((r + 1) % 6) := by
  have h8 := packed_get_join8 (S := 64) c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_34 (idx : Nat) (hlo : 17408 ≤ idx) (hhi : idx < 17920) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_34.get 32 ⟨idx - 17408, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c2Pair_pat512_p3 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p3 c2Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p5 c2Pair_c64_p3)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p1 c2Pair_c64_p5) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p3 c2Pair_c64_p1))

private theorem c2Pair_eval512_p3 (r : Nat) (hhi : r < 512) :
    c2Pair_pat512_p3.get 32 ⟨r, hhi⟩ = c2PairWord ((r + 3) % 6) := by
  have h8 := packed_get_join8 (S := 64) c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_35 (idx : Nat) (hlo : 17920 ≤ idx) (hhi : idx < 18432) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_35.get 32 ⟨idx - 17920, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c2Pair_pat512_p5 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p5 c2Pair_c64_p3) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p1 c2Pair_c64_p5)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p3 c2Pair_c64_p1) (@ArtifactEncoding.Packed.join 64 64 c2Pair_c64_p5 c2Pair_c64_p3))

private theorem c2Pair_eval512_p5 (r : Nat) (hhi : r < 512) :
    c2Pair_pat512_p5.get 32 ⟨r, hhi⟩ = c2PairWord ((r + 5) % 6) := by
  have h8 := packed_get_join8 (S := 64) c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 c2Pair_c64_p1 c2Pair_c64_p5 c2Pair_c64_p3 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c2Pair_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c2Pair_chunk64_p5 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c2Pair_chunk64_p3 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_36 (idx : Nat) (hlo : 18432 ≤ idx) (hhi : idx < 18944) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_36.get 32 ⟨idx - 18432, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_37 (idx : Nat) (hlo : 18944 ≤ idx) (hhi : idx < 19456) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_37.get 32 ⟨idx - 18944, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_38 (idx : Nat) (hlo : 19456 ≤ idx) (hhi : idx < 19968) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_38.get 32 ⟨idx - 19456, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_39 (idx : Nat) (hlo : 19968 ≤ idx) (hhi : idx < 20480) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_39.get 32 ⟨idx - 19968, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_4 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39 (idx - 16384) (by omega)
  have hdef : MoonArtifact.commitCode_1_4 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_32 MoonArtifact.commitCode_0_33) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_34 MoonArtifact.commitCode_0_35)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_36 MoonArtifact.commitCode_0_37) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_38 MoonArtifact.commitCode_0_39))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 16384) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_40 (idx : Nat) (hlo : 20480 ≤ idx) (hhi : idx < 20992) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_40.get 32 ⟨idx - 20480, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_41 (idx : Nat) (hlo : 20992 ≤ idx) (hhi : idx < 21504) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_41.get 32 ⟨idx - 20992, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_42 (idx : Nat) (hlo : 21504 ≤ idx) (hhi : idx < 22016) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_42.get 32 ⟨idx - 21504, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_43 (idx : Nat) (hlo : 22016 ≤ idx) (hhi : idx < 22528) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_43.get 32 ⟨idx - 22016, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_44 (idx : Nat) (hlo : 22528 ≤ idx) (hhi : idx < 23040) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_44.get 32 ⟨idx - 22528, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem c2Pair_bnd64_352 (i : Fin 49) :
    (ArtifactEncoding.Packed.chunk 64 51796116474899734880761154390461101025774278186434407077114841220993009821989801411410621923063345558391907829892861680389233520910177881952451657613154040969627658394402418588976476795605265010833697948489458086565415793087144828084362377024600009564449746046951557140045655376296718751221199750708093672055413195837804267916337089139255754173349419939231505766928549830473354074911461517386730169803443146123491994179903318567336933892746393853103629644966548244272430908384008038328841352830580843254523617061944508453680625699098201941362201326813401827628150560564972488976502462554543168476476732829750788211).get 32 ⟨0 + i.val, by omega⟩ =
      c2PairWord ((5 + i.val) % 6) := by
  revert i; decide

private theorem c2Pair_blk512_44 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 49) :
    MoonArtifact.commitCode_0_44.get 32 ⟨r, by omega⟩ = c2PairWord ((22528 + r - 16433) % 6) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c2Pair_bnd64_352 ⟨r - 0 - 0, by omega⟩
    dsimp only at h
    have heq2 : (5 + (r - 0 - 0)) % 6 = (22528 + r - 16433) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_c2Pair (state : MachineState) (k j : Nat) (hk : k < 1024) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (c2PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (16433 + 6 * k + j) (by omega)
    (c2PairWord j) hpc _ (c2PairInstr j) (decode_c2PairWord ⟨j, hj⟩)
  have hb_lo : 32 ≤ (16433 + 6 * k + j) / 512 := by omega
  have hb_hi : (16433 + 6 * k + j) / 512 ≤ 44 := by omega
  generalize hbv : (16433 + 6 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_32 (16433 + 6 * k + j) (by omega) (by omega)]
    rw [c2Pair_blk512_32 (16433 + 6 * k + j - 16384) (by omega) (by omega)]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_33 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_33 = c2Pair_pat512_p1 := rfl
    rw [hpat, c2Pair_eval512_p1]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_34 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_34 = c2Pair_pat512_p3 := rfl
    rw [hpat, c2Pair_eval512_p3]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_35 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_35 = c2Pair_pat512_p5 := rfl
    rw [hpat, c2Pair_eval512_p5]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_36 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_36 = c2Pair_pat512_p1 := rfl
    rw [hpat, c2Pair_eval512_p1]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_37 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_37 = c2Pair_pat512_p3 := rfl
    rw [hpat, c2Pair_eval512_p3]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_38 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_38 = c2Pair_pat512_p5 := rfl
    rw [hpat, c2Pair_eval512_p5]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_39 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_39 = c2Pair_pat512_p1 := rfl
    rw [hpat, c2Pair_eval512_p1]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_40 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_40 = c2Pair_pat512_p3 := rfl
    rw [hpat, c2Pair_eval512_p3]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_41 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_41 = c2Pair_pat512_p5 := rfl
    rw [hpat, c2Pair_eval512_p5]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_42 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_42 = c2Pair_pat512_p1 := rfl
    rw [hpat, c2Pair_eval512_p1]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_43 (16433 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_43 = c2Pair_pat512_p3 := rfl
    rw [hpat, c2Pair_eval512_p3]
    exact congrArg c2PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_44 (16433 + 6 * k + j) (by omega) (by omega)]
    rw [c2Pair_blk512_44 (16433 + 6 * k + j - 22528) (by omega) (by omega)]
    exact congrArg c2PairWord (by omega)

def c3PairWord : Nat → BitVec 32
  | 0 => (67437843#32)
  | 1 => (33949203#32)
  | 2 => (115#32)
  | 3 => (59049235#32)
  | 4 => (33949203#32)
  | 5 => (115#32)
  | _ => 0#32

def c3PairInstr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (64#12))
  | 1 => .base (.ADDI .x12 .x12 (32#12))
  | 2 => .base .ECALL
  | 3 => .base (.ADDI .x10 .x10 (56#12))
  | 4 => .base (.ADDI .x12 .x12 (32#12))
  | 5 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_c3PairWord (j : Fin 6) :
    decodeInstruction (c3PairWord j.val) = some (c3PairInstr j.val) := by
  revert j; decide

private abbrev c3Pair_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 444309433456806301500386707256861626059431176643362107376462093939712012233483141800868322974100873996204213328892047173308238322099249069102052411292339486085224358606046006692991941093520749460887691451769934730573739185909215722226836783794000787462682002619315071085938452284433189189164435159059487614990603903821154761225412478838122286380944401949039863617356778759231645699398179960488290720576092219230081278390379713557919979957999210117706480375408765856017482401916674344312374249627541978601600924974834958675819235722504593118721868179284944926086819877053877284090252032887343192233992219076111697171

private theorem c3Pair_chunk64_p0 (i : Fin 64) :
    c3Pair_c64_p0.get 32 i =
      c3PairWord ((i.val + 0) % 6) := by
  revert i; decide

private abbrev c3Pair_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 255447020748303842015165604292000515827440717714129424440277443678007653193093711653599317268989474376202630060444618717622160968435049372362301968219295924148446868993357291687825814868006106026488341526601870343048720205043474137937573136591928324448904408922623196275076303166127441220020047730957169220267955695076428026847171131122517258662491620376602207172976947084799520329192806749373206110927389634466895737321407813139359666286484016369209455312947897728482583955843379786463250184557274864286491033892439510297678251600414419945005402994099485642787948369617602679232942103006064400421972132052240565779

private theorem c3Pair_chunk64_p4 (i : Fin 64) :
    c3Pair_c64_p4.get 32 i =
      c3PairWord ((i.val + 4) % 6) := by
  revert i; decide

private abbrev c3Pair_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 865364248217432631028659286523104248499014498408911106801041186290973509540800401831539855366126346834783926443630562003216468885117587853166716639608025363338530708700186528699212341709216070065976420104435749885445307241518962266352093185829253307186703646047984387763120820144481257918686632725422729371529327333240396409708315921485343980781985722632809947877763709673888861491723459520488829989821258907707408669899405121424691054648295690337351053555504753244984622435291125668343301382245338483528089998869169338634991129347877512463960304688683906458930552635418285357032486380841873946291381299314803

private theorem c3Pair_chunk64_p2 (i : Fin 64) :
    c3Pair_c64_p2.get 32 i =
      c3PairWord ((i.val + 2) % 6) := by
  revert i; decide

private theorem c3Pair_blk512_44 (r : Nat) (hlo : 64 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_44.get 32 ⟨r, by omega⟩ = c3PairWord ((22528 + r - 22592) % 6) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p0 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 0) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p4 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 4) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p2 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 2) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p0 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 0) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p4 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 4) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p2 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 2) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_44
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p0 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 0) % 6 = (22528 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_45 (idx : Nat) (hlo : 23040 ≤ idx) (hhi : idx < 23552) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_45.get 32 ⟨idx - 23040, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c3Pair_pat512_p4 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p4 c3Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p0 c3Pair_c64_p4)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p2 c3Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p4 c3Pair_c64_p2))

private theorem c3Pair_eval512_p4 (r : Nat) (hhi : r < 512) :
    c3Pair_pat512_p4.get 32 ⟨r, hhi⟩ = c3PairWord ((r + 4) % 6) := by
  have h8 := packed_get_join8 (S := 64) c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_46 (idx : Nat) (hlo : 23552 ≤ idx) (hhi : idx < 24064) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_46.get 32 ⟨idx - 23552, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c3Pair_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p0 c3Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p2 c3Pair_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p4 c3Pair_c64_p2) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p0 c3Pair_c64_p4))

private theorem c3Pair_eval512_p0 (r : Nat) (hhi : r < 512) :
    c3Pair_pat512_p0.get 32 ⟨r, hhi⟩ = c3PairWord ((r + 0) % 6) := by
  have h8 := packed_get_join8 (S := 64) c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_47 (idx : Nat) (hlo : 24064 ≤ idx) (hhi : idx < 24576) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_47.get 32 ⟨idx - 24064, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_5 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47 (idx - 20480) (by omega)
  have hdef : MoonArtifact.commitCode_1_5 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_40 MoonArtifact.commitCode_0_41) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_42 MoonArtifact.commitCode_0_43)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_44 MoonArtifact.commitCode_0_45) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_46 MoonArtifact.commitCode_0_47))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 20480) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev c3Pair_pat512_p2 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p2 c3Pair_c64_p0) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p4 c3Pair_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p0 c3Pair_c64_p4) (@ArtifactEncoding.Packed.join 64 64 c3Pair_c64_p2 c3Pair_c64_p0))

private theorem c3Pair_eval512_p2 (r : Nat) (hhi : r < 512) :
    c3Pair_pat512_p2.get 32 ⟨r, hhi⟩ = c3PairWord ((r + 2) % 6) := by
  have h8 := packed_get_join8 (S := 64) c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 c3Pair_c64_p4 c3Pair_c64_p2 c3Pair_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, c3Pair_chunk64_p4 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, c3Pair_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, c3Pair_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_48 (idx : Nat) (hlo : 24576 ≤ idx) (hhi : idx < 25088) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_48.get 32 ⟨idx - 24576, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_49 (idx : Nat) (hlo : 25088 ≤ idx) (hhi : idx < 25600) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_49.get 32 ⟨idx - 25088, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_50 (idx : Nat) (hlo : 25600 ≤ idx) (hhi : idx < 26112) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_50.get 32 ⟨idx - 25600, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_51 (idx : Nat) (hlo : 26112 ≤ idx) (hhi : idx < 26624) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_51.get 32 ⟨idx - 26112, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_52 (idx : Nat) (hlo : 26624 ≤ idx) (hhi : idx < 27136) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_52.get 32 ⟨idx - 26624, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_53 (idx : Nat) (hlo : 27136 ≤ idx) (hhi : idx < 27648) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_53.get 32 ⟨idx - 27136, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_54 (idx : Nat) (hlo : 27648 ≤ idx) (hhi : idx < 28160) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_54.get 32 ⟨idx - 27648, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_55 (idx : Nat) (hlo : 28160 ≤ idx) (hhi : idx < 28672) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_55.get 32 ⟨idx - 28160, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_6 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55 (idx - 24576) (by omega)
  have hdef : MoonArtifact.commitCode_1_6 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_48 MoonArtifact.commitCode_0_49) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_50 MoonArtifact.commitCode_0_51)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_52 MoonArtifact.commitCode_0_53) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_54 MoonArtifact.commitCode_0_55))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 24576) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_56 (idx : Nat) (hlo : 28672 ≤ idx) (hhi : idx < 29184) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_56.get 32 ⟨idx - 28672, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem c3Pair_blk512_56 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 64) :
    MoonArtifact.commitCode_0_56.get 32 ⟨r, by omega⟩ = c3PairWord ((28672 + r - 22592) % 6) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := c3Pair_chunk64_p2 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 2) % 6 = (28672 + r - 22592) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_c3Pair (state : MachineState) (k j : Nat) (hk : k < 1024) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (c3PairInstr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (22592 + 6 * k + j) (by omega)
    (c3PairWord j) hpc _ (c3PairInstr j) (decode_c3PairWord ⟨j, hj⟩)
  have hb_lo : 44 ≤ (22592 + 6 * k + j) / 512 := by omega
  have hb_hi : (22592 + 6 * k + j) / 512 ≤ 56 := by omega
  generalize hbv : (22592 + 6 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_44 (22592 + 6 * k + j) (by omega) (by omega)]
    rw [c3Pair_blk512_44 (22592 + 6 * k + j - 22528) (by omega) (by omega)]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_45 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_45 = c3Pair_pat512_p4 := rfl
    rw [hpat, c3Pair_eval512_p4]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_46 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_46 = c3Pair_pat512_p0 := rfl
    rw [hpat, c3Pair_eval512_p0]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_47 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_47 = c3Pair_pat512_p2 := rfl
    rw [hpat, c3Pair_eval512_p2]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_48 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_48 = c3Pair_pat512_p4 := rfl
    rw [hpat, c3Pair_eval512_p4]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_49 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_49 = c3Pair_pat512_p0 := rfl
    rw [hpat, c3Pair_eval512_p0]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_50 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_50 = c3Pair_pat512_p2 := rfl
    rw [hpat, c3Pair_eval512_p2]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_51 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_51 = c3Pair_pat512_p4 := rfl
    rw [hpat, c3Pair_eval512_p4]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_52 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_52 = c3Pair_pat512_p0 := rfl
    rw [hpat, c3Pair_eval512_p0]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_53 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_53 = c3Pair_pat512_p2 := rfl
    rw [hpat, c3Pair_eval512_p2]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_54 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_54 = c3Pair_pat512_p4 := rfl
    rw [hpat, c3Pair_eval512_p4]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_55 (22592 + 6 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_55 = c3Pair_pat512_p0 := rfl
    rw [hpat, c3Pair_eval512_p0]
    exact congrArg c3PairWord (by omega)
  · rw [get_commitCode_to_commitCode_0_56 (22592 + 6 * k + j) (by omega) (by omega)]
    rw [c3Pair_blk512_56 (22592 + 6 * k + j - 28672) (by omega) (by omega)]
    exact congrArg c3PairWord (by omega)

def l1Word : Nat → BitVec 32
  | 0 => (4228187411#32)
  | 1 => (4261807635#32)
  | 2 => (115#32)
  | _ => 0#32

def l1Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (4032#12))
  | 1 => .base (.ADDI .x12 .x12 (4064#12))
  | 2 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_l1Word (j : Fin 3) :
    decodeInstruction (l1Word j.val) = some (l1Instr j.val) := by
  revert j; decide

private abbrev l1_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 872771068960486484783241613457351200262233559741632510010213819535750453822076202343546599517170166612689161543912528521825309079247810726043896388659079509838910039974748578925644799498238832516245687708082197537110277421370936470200622956488795941812068424451963203240757954412420399019797798494280372502601661338575119026396894822068021095091883745416804122307644489053588365576228746796596625373832457213523600235942823979618508527089310105599155734345599428609103351272851739445847750029197370296067913137997907683826214352763064091208167304037925552302557213611115533164034666123629124181616151731634291

private theorem l1_chunk64_p2 (i : Fin 64) :
    l1_c64_p2.get 32 i =
      l1Word ((i.val + 2) % 3) := by
  revert i; decide

private abbrev l1_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 31814528217522373936926667083971701095897270910123759135291587046667390912885659514574428640936691171666058344363636750015437242677785476872081667907405869042759681754137017894957314026473701537649500637614339914034820052424837345763494011590516145133372912492611495663728911412154380018411889417543785857200141377593163667593626029548357182898018587109676502015157587398796370704044974629551077755394306712414030371273595473516424025753360042000675562489645983482798867218058666632358832354743684834661850166310027800125466734020481403305292450770816204714050084685105143754740957245798470610586010239830418782487827

private theorem l1_chunk64_p0 (i : Fin 64) :
    l1_c64_p0.get 32 i =
      l1Word ((i.val + 0) % 3) := by
  revert i; decide

private abbrev l1_c64_p1 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 32067499879484328811813559468552420461567955986693176449271256707958761013168039167733039253120207744168481938746905644083175418154763422021412925261699229349277952737983261756846488262603002972949988993074462949869282726374111665793973308021449956383463588151253600982385400925981942003433475166480248618351662024635860079303251876278964198949286557536636557470369480456724009434521726379167531905193809491919637509929199122222254297631027695744255138703385475801266207859153869458236182671988648351800491925894228155930409106742572665096254304804593697234706484053805872482920669371696684150905212947471199172429331

private theorem l1_chunk64_p1 (i : Fin 64) :
    l1_c64_p1.get 32 i =
      l1Word ((i.val + 1) % 3) := by
  revert i; decide

private theorem l1_bnd64_449 (i : Fin 53) :
    (ArtifactEncoding.Packed.chunk 64 32067499879484328811813559468552420461567955986693176449271256707958761013168039167733039253120207744168481938746905644083175418154763422021412925261699229349277952737983261756846488262603002972949988993074462949869282726374111665793973308021449956383463588151253600982385400925981942003433475166480248618351662024635860079303251876278964198949286557536636557470369480456724009434521726379167531905193809491919637509929199122222254297631027695744255138703385475801266207859153869458236182671988648351800491925894242229382983417849536289336246098398745461994221606535824134739517511637071786329589214161650551241376867).get 32 ⟨11 + i.val, by omega⟩ =
      l1Word ((0 + i.val) % 3) := by
  revert i; decide

private theorem l1_blk512_56 (r : Nat) (hlo : 75 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_56.get 32 ⟨r, by omega⟩ = l1Word ((28672 + r - 28747) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l1_bnd64_449 ⟨r - 64 - 11, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 64 - 11)) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p2 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 2) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p0 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 0) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p1 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 1) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p2 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 2) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p0 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 0) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_56
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p1 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 1) % 3 = (28672 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_57 (idx : Nat) (hlo : 29184 ≤ idx) (hhi : idx < 29696) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_57.get 32 ⟨idx - 29184, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev l1_pat512_p2 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p2 l1_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p1 l1_c64_p2)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p0 l1_c64_p1) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p2 l1_c64_p0))

private theorem l1_eval512_p2 (r : Nat) (hhi : r < 512) :
    l1_pat512_p2.get 32 ⟨r, hhi⟩ = l1Word ((r + 2) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1_c64_p2 l1_c64_p0 l1_c64_p1 l1_c64_p2 l1_c64_p0 l1_c64_p1 l1_c64_p2 l1_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_58 (idx : Nat) (hlo : 29696 ≤ idx) (hhi : idx < 30208) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_58.get 32 ⟨idx - 29696, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev l1_pat512_p1 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p1 l1_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p0 l1_c64_p1)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p2 l1_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p1 l1_c64_p2))

private theorem l1_eval512_p1 (r : Nat) (hhi : r < 512) :
    l1_pat512_p1.get 32 ⟨r, hhi⟩ = l1Word ((r + 1) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1_c64_p1 l1_c64_p2 l1_c64_p0 l1_c64_p1 l1_c64_p2 l1_c64_p0 l1_c64_p1 l1_c64_p2 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_59 (idx : Nat) (hlo : 30208 ≤ idx) (hhi : idx < 30720) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_59.get 32 ⟨idx - 30208, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev l1_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p0 l1_c64_p1) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p2 l1_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l1_c64_p1 l1_c64_p2) (@ArtifactEncoding.Packed.join 64 64 l1_c64_p0 l1_c64_p1))

private theorem l1_eval512_p0 (r : Nat) (hhi : r < 512) :
    l1_pat512_p0.get 32 ⟨r, hhi⟩ = l1Word ((r + 0) % 3) := by
  have h8 := packed_get_join8 (S := 64) l1_c64_p0 l1_c64_p1 l1_c64_p2 l1_c64_p0 l1_c64_p1 l1_c64_p2 l1_c64_p0 l1_c64_p1 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, l1_chunk64_p2 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, l1_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, l1_chunk64_p1 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_60 (idx : Nat) (hlo : 30720 ≤ idx) (hhi : idx < 31232) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_60.get 32 ⟨idx - 30720, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_61 (idx : Nat) (hlo : 31232 ≤ idx) (hhi : idx < 31744) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_61.get 32 ⟨idx - 31232, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_62 (idx : Nat) (hlo : 31744 ≤ idx) (hhi : idx < 32256) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_62.get 32 ⟨idx - 31744, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_63 (idx : Nat) (hlo : 32256 ≤ idx) (hhi : idx < 32768) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_63.get 32 ⟨idx - 32256, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_7 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63 (idx - 28672) (by omega)
  have hdef : MoonArtifact.commitCode_1_7 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_56 MoonArtifact.commitCode_0_57) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_58 MoonArtifact.commitCode_0_59)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_60 MoonArtifact.commitCode_0_61) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_62 MoonArtifact.commitCode_0_63))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 28672) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_64 (idx : Nat) (hlo : 32768 ≤ idx) (hhi : idx < 33280) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_64.get 32 ⟨idx - 32768, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_65 (idx : Nat) (hlo : 33280 ≤ idx) (hhi : idx < 33792) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_65.get 32 ⟨idx - 33280, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_66 (idx : Nat) (hlo : 33792 ≤ idx) (hhi : idx < 34304) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_66.get 32 ⟨idx - 33792, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_67 (idx : Nat) (hlo : 34304 ≤ idx) (hhi : idx < 34816) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_67.get 32 ⟨idx - 34304, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_68 (idx : Nat) (hlo : 34816 ≤ idx) (hhi : idx < 35328) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_68.get 32 ⟨idx - 34816, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem l1_bnd64_545 (i : Fin 11) :
    (ArtifactEncoding.Packed.chunk 64 3018687179948185071586831407757060429734698436655441245530478413419818422953412071608963548065745490574775671235408796767012026270970932028545763518435494853861882346202544228260764603254282555496638940612810193964290754606733801332139557410838239489698686247752141856278190313082282692726703078010739173932073895068825839267422987718776864049513280097295941727509660382616540376930688042988627953464955593764939030990695517697301676899978974063488058353858570130405100110356160963995340265620987494014887938939103316282658496662876037157336156503722483236662087304485022488892060883532516617681783292121231787539).get 32 ⟨0 + i.val, by omega⟩ =
      l1Word ((1 + i.val) % 3) := by
  revert i; decide

private theorem l1_blk512_68 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 75) :
    MoonArtifact.commitCode_0_68.get 32 ⟨r, by omega⟩ = l1Word ((34816 + r - 28747) % 3) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l1_chunk64_p0 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 0) % 3 = (34816 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l1_bnd64_545 ⟨r - 64 - 0, by omega⟩
    dsimp only at h
    have heq2 : (1 + (r - 64 - 0)) % 3 = (34816 + r - 28747) % 3 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_l1 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 3)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * k + j))) :
    fetch (submission.image .commit) state = some (l1Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (28747 + 3 * k + j) (by omega)
    (l1Word j) hpc _ (l1Instr j) (decode_l1Word ⟨j, hj⟩)
  have hb_lo : 56 ≤ (28747 + 3 * k + j) / 512 := by omega
  have hb_hi : (28747 + 3 * k + j) / 512 ≤ 68 := by omega
  generalize hbv : (28747 + 3 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_56 (28747 + 3 * k + j) (by omega) (by omega)]
    rw [l1_blk512_56 (28747 + 3 * k + j - 28672) (by omega) (by omega)]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_57 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_57 = l1_pat512_p2 := rfl
    rw [hpat, l1_eval512_p2]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_58 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_58 = l1_pat512_p1 := rfl
    rw [hpat, l1_eval512_p1]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_59 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_59 = l1_pat512_p0 := rfl
    rw [hpat, l1_eval512_p0]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_60 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_60 = l1_pat512_p2 := rfl
    rw [hpat, l1_eval512_p2]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_61 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_61 = l1_pat512_p1 := rfl
    rw [hpat, l1_eval512_p1]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_62 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_62 = l1_pat512_p0 := rfl
    rw [hpat, l1_eval512_p0]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_63 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_63 = l1_pat512_p2 := rfl
    rw [hpat, l1_eval512_p2]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_64 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_64 = l1_pat512_p1 := rfl
    rw [hpat, l1_eval512_p1]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_65 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_65 = l1_pat512_p0 := rfl
    rw [hpat, l1_eval512_p0]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_66 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_66 = l1_pat512_p2 := rfl
    rw [hpat, l1_eval512_p2]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_67 (28747 + 3 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_67 = l1_pat512_p1 := rfl
    rw [hpat, l1_eval512_p1]
    exact congrArg l1Word (by omega)
  · rw [get_commitCode_to_commitCode_0_68 (28747 + 3 * k + j) (by omega) (by omega)]
    rw [l1_blk512_68 (28747 + 3 * k + j - 34816) (by omega) (by omega)]
    exact congrArg l1Word (by omega)

def l25Word : Nat → BitVec 32
  | 0 => (4228187411#32)
  | 1 => (4261807635#32)
  | 2 => (115#32)
  | 3 => (401187#32)
  | _ => 0#32

def l25Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (4032#12))
  | 1 => .base (.ADDI .x12 .x12 (4064#12))
  | 2 => .base .ECALL
  | 3 => .base (.SH .x12 .x0 (30#12))
  | _ => .base .EBREAK

private theorem decode_l25Word (j : Fin 4) :
    decodeInstruction (l25Word j.val) = some (l25Instr j.val) := by
  revert j; decide

private abbrev l25_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 3018687179948185071586831407757060429734698436655441245530478413419818422953412071608963548065745490574775671235408796767012026270970932028545763518435494853861882346202544228260764603254282555496638940612810193964290754606733801332139557410838239489698686247752141856278190313082282692726703078010739173932073895068825839267422987718776864049513280097295941727509660382616540376930688042988627953464955593764939030990695517697301676899978974063488058353858570111088768970075844643693761651014314948235862753638348260442220539374385988965136408312305323939655533690489684941330483303455384882437168029276658009363

private theorem l25_chunk64_p0 (i : Fin 64) :
    l25_c64_p0.get 32 i =
      l25Word ((i.val + 0) % 4) := by
  revert i; decide

private theorem l25_bnd64_545 (i : Fin 48) :
    (ArtifactEncoding.Packed.chunk 64 3018687179948185071586831407757060429734698436655441245530478413419818422953412071608963548065745490574775671235408796767012026270970932028545763518435494853861882346202544228260764603254282555496638940612810193964290754606733801332139557410838239489698686247752141856278190313082282692726703078010739173932073895068825839267422987718776864049513280097295941727509660382616540376930688042988627953464955593764939030990695517697301676899978974063488058353858570130405100110356160963995340265620987494014887938939103316282658496662876037157336156503722483236662087304485022488892060883532516617681783292121231787539).get 32 ⟨16 + i.val, by omega⟩ =
      l25Word ((0 + i.val) % 4) := by
  revert i; decide

private theorem l25_blk512_68 (r : Nat) (hlo : 80 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_68.get 32 ⟨r, by omega⟩ = l25Word ((34816 + r - 34896) % 4) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l25_bnd64_545 ⟨r - 64 - 16, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 64 - 16)) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_68
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 0) % 4 = (34816 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_69 (idx : Nat) (hlo : 35328 ≤ idx) (hhi : idx < 35840) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_69.get 32 ⟨idx - 35328, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private abbrev l25_pat512_p0 : ArtifactEncoding.Packed 512 :=
  @ArtifactEncoding.Packed.join 256 256 (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l25_c64_p0 l25_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l25_c64_p0 l25_c64_p0)) (@ArtifactEncoding.Packed.join 128 128 (@ArtifactEncoding.Packed.join 64 64 l25_c64_p0 l25_c64_p0) (@ArtifactEncoding.Packed.join 64 64 l25_c64_p0 l25_c64_p0))

private theorem l25_eval512_p0 (r : Nat) (hhi : r < 512) :
    l25_pat512_p0.get 32 ⟨r, hhi⟩ = l25Word ((r + 0) % 4) := by
  have h8 := packed_get_join8 (S := 64) l25_c64_p0 l25_c64_p0 l25_c64_p0 l25_c64_p0 l25_c64_p0 l25_c64_p0 l25_c64_p0 l25_c64_p0 r (by omega)
  rw [h8]
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · rw [pick8_0, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_1, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_2, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_3, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_4, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_5, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_6, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)
  · rw [pick8_7, l25_chunk64_p0 ⟨r % 64, by omega⟩]
    exact congrArg _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_70 (idx : Nat) (hlo : 35840 ≤ idx) (hhi : idx < 36352) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_70.get 32 ⟨idx - 35840, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_71 (idx : Nat) (hlo : 36352 ≤ idx) (hhi : idx < 36864) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_71.get 32 ⟨idx - 36352, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_8 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71 (idx - 32768) (by omega)
  have hdef : MoonArtifact.commitCode_1_8 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_64 MoonArtifact.commitCode_0_65) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_66 MoonArtifact.commitCode_0_67)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_68 MoonArtifact.commitCode_0_69) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_70 MoonArtifact.commitCode_0_71))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 32768) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_72 (idx : Nat) (hlo : 36864 ≤ idx) (hhi : idx < 37376) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_72.get 32 ⟨idx - 36864, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 0 := by omega
  rw [hqd, pick8_0]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_73 (idx : Nat) (hlo : 37376 ≤ idx) (hhi : idx < 37888) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_73.get 32 ⟨idx - 37376, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 1 := by omega
  rw [hqd, pick8_1]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_74 (idx : Nat) (hlo : 37888 ≤ idx) (hhi : idx < 38400) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_74.get 32 ⟨idx - 37888, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 2 := by omega
  rw [hqd, pick8_2]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_75 (idx : Nat) (hlo : 38400 ≤ idx) (hhi : idx < 38912) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_75.get 32 ⟨idx - 38400, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 3 := by omega
  rw [hqd, pick8_3]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_76 (idx : Nat) (hlo : 38912 ≤ idx) (hhi : idx < 39424) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_76.get 32 ⟨idx - 38912, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 4 := by omega
  rw [hqd, pick8_4]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_77 (idx : Nat) (hlo : 39424 ≤ idx) (hhi : idx < 39936) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_77.get 32 ⟨idx - 39424, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 5 := by omega
  rw [hqd, pick8_5]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_78 (idx : Nat) (hlo : 39936 ≤ idx) (hhi : idx < 40448) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_78.get 32 ⟨idx - 39936, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 6 := by omega
  rw [hqd, pick8_6]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_79 (idx : Nat) (hlo : 40448 ≤ idx) (hhi : idx < 40960) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_79.get 32 ⟨idx - 40448, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_9 idx (by omega) (by omega)]
  have h8 := packed_get_join8 (S := 512) MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79 (idx - 36864) (by omega)
  have hdef : MoonArtifact.commitCode_1_9 = (@ArtifactEncoding.Packed.join 2048 2048 (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_72 MoonArtifact.commitCode_0_73) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_74 MoonArtifact.commitCode_0_75)) (@ArtifactEncoding.Packed.join 1024 1024 (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_76 MoonArtifact.commitCode_0_77) (@ArtifactEncoding.Packed.join 512 512 MoonArtifact.commitCode_0_78 MoonArtifact.commitCode_0_79))) := rfl
  rw [hdef, h8]
  have hqd : (idx - 36864) / 512 = 7 := by omega
  rw [hqd, pick8_7]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_80 (idx : Nat) (hlo : 40960 ≤ idx) (hhi : idx < 41472) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_80.get 32 ⟨idx - 40960, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_81 (idx : Nat) (hlo : 41472 ≤ idx) (hhi : idx < 41984) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_81.get 32 ⟨idx - 41472, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_82 (idx : Nat) (hlo : 41984 ≤ idx) (hhi : idx < 42496) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_82.get 32 ⟨idx - 41984, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_83 (idx : Nat) (hlo : 42496 ≤ idx) (hhi : idx < 43008) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_83.get 32 ⟨idx - 42496, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_84 (idx : Nat) (hlo : 43008 ≤ idx) (hhi : idx < 43520) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_84.get 32 ⟨idx - 43008, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem l25_bnd64_673 (i : Fin 16) :
    (ArtifactEncoding.Packed.chunk 64 192414428721919425589654724565787467430338830875190523910610161370861533781906010276771907972769451025871696136963853702938711237605720821304528535186981971231346965073300964678701171472570645837423019206438983703330273861556051496545137830704963864973973233308226184140391876891324767796105025244391870346022755226592176190508836398744011315530786605551230712994765250487384830904258568772442756486957127278007492841383937776867785897582325078466335842332281730880476034887434104478851852141658829135671665664885158964207765996746083185974219767962808095118089837774709540834189595535571334939791902863659266016531).get 32 ⟨0 + i.val, by omega⟩ =
      l25Word ((0 + i.val) % 4) := by
  revert i; decide

private theorem l25_blk512_84 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 80) :
    MoonArtifact.commitCode_0_84.get 32 ⟨r, by omega⟩ = l25Word ((43008 + r - 34896) % 4) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l25_chunk64_p0 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 0) % 4 = (43008 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l25_bnd64_673 ⟨r - 64 - 0, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 64 - 0)) % 4 = (43008 + r - 34896) % 4 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem commit_fetch_l25 (state : MachineState) (k j : Nat) (hk : k < 2048) (hj : j < 4)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k + j))) :
    fetch (submission.image .commit) state = some (l25Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (34896 + 4 * k + j) (by omega)
    (l25Word j) hpc _ (l25Instr j) (decode_l25Word ⟨j, hj⟩)
  have hb_lo : 68 ≤ (34896 + 4 * k + j) / 512 := by omega
  have hb_hi : (34896 + 4 * k + j) / 512 ≤ 84 := by omega
  generalize hbv : (34896 + 4 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_68 (34896 + 4 * k + j) (by omega) (by omega)]
    rw [l25_blk512_68 (34896 + 4 * k + j - 34816) (by omega) (by omega)]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_69 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_69 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_70 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_70 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_71 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_71 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_72 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_72 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_73 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_73 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_74 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_74 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_75 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_75 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_76 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_76 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_77 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_77 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_78 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_78 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_79 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_79 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_80 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_80 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_81 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_81 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_82 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_82 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_83 (34896 + 4 * k + j) (by omega) (by omega)]
    have hpat : MoonArtifact.commitCode_0_83 = l25_pat512_p0 := rfl
    rw [hpat, l25_eval512_p0]
    exact congrArg l25Word (by omega)
  · rw [get_commitCode_to_commitCode_0_84 (34896 + 4 * k + j) (by omega) (by omega)]
    rw [l25_blk512_84 (34896 + 4 * k + j - 43008) (by omega) (by omega)]
    exact congrArg l25Word (by omega)

def l623Word : Nat → BitVec 32
  | 0 => (4228187411#32)
  | 1 => (4261807635#32)
  | 2 => (115#32)
  | 3 => (25572099#32)
  | 4 => (28537651#32)
  | 5 => (6700067#32)
  | _ => 0#32

def l623Instr : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (4032#12))
  | 1 => .base (.ADDI .x12 .x12 (4064#12))
  | 2 => .base .ECALL
  | 3 => .base (.LD .x6 .x12 (24#12))
  | 4 => .base (.AND .x6 .x6 .x27)
  | 5 => .base (.SD .x12 .x6 (24#12))
  | _ => .base .EBREAK

private theorem decode_l623Word (j : Fin 6) :
    decodeInstruction (l623Word j.val) = some (l623Instr j.val) := by
  revert j; decide

private abbrev l623_c64_p4 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 32067499879484328811816292364920801312085248633863566740286957366366812728226670236681580982379874094823925820384846863739913962246490451185287208112820518680179546704009443627262187083877377505386376999723543664397811750162814668991390139844747393909921182251954613154848126388177514716483426842484656424020089263836247463493538630234681929468135970573217676018108623367835387385465976912798973086726223768010083864391227705676032690247937741721021711683075632854172630418916889582380675056129938497980995261685256652510212216285871666209757437357753722681924360071699171054258823205796649647754354421529809125602099

private theorem l623_chunk64_p4 (i : Fin 64) :
    l623_c64_p4.get 32 i =
      l623Word ((i.val + 4) % 6) := by
  revert i; decide

private abbrev l623_c64_p2 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 50413912658560770407597070226490212986489791005386015413494610665409231684619958826682175063798108209013364744326086724896760500462390834592038539687207175560082560869556378156193265706497287187454241136573283603623186919907490424026798109126146575898046465057388514723144599618777923940230979384344240649572001582937506257389559238478622302996096918163404475281883173416625527516597119846047603674954622184870839012871905926111247485578901393971889493281263729300275197982579660147388139054886084658868986592983492993514822729424356726216521943563918037760844137366455765064160249597363773068580551512314884391027

private theorem l623_chunk64_p2 (i : Fin 64) :
    l623_c64_p2.get 32 i =
      l623Word ((i.val + 2) % 6) := by
  revert i; decide

private abbrev l623_c64_p0 : ArtifactEncoding.Packed 64 :=
  ArtifactEncoding.Packed.chunk 64 192414428721919425589654724565787467430338830875190523910610161370861533781906010276771907972769451025871696136963853702938711237605720821304528535186981971231346965073300964678701171472570645837423019206438983703330273861556051496545137830704963864973973233308226184140391876891324767796105025244391870346022755226592176190508836398744011315530786605551230712994765250487384830904258568812644426476041452685273938825273236746006769514649018041875922501237556836125864909083574679863264888235527829943159325190528340914877254049441159415723886578571154437621009387049950073275408970523039782961222984468498718459155

private theorem l623_chunk64_p0 (i : Fin 64) :
    l623_c64_p0.get 32 i =
      l623Word ((i.val + 0) % 6) := by
  revert i; decide

private theorem l623_bnd64_673 (i : Fin 40) :
    (ArtifactEncoding.Packed.chunk 64 192414428721919425589654724565787467430338830875190523910610161370861533781906010276771907972769451025871696136963853702938711237605720821304528535186981971231346965073300964678701171472570645837423019206438983703330273861556051496545137830704963864973973233308226184140391876891324767796105025244391870346022755226592176190508836398744011315530786605551230712994765250487384830904258568772442756486957127278007492841383937776867785897582325078466335842332281730880476034887434104478851852141658829135671665664885158964207765996746083185974219767962808095118089837774709540834189595535571334939791902863659266016531).get 32 ⟨24 + i.val, by omega⟩ =
      l623Word ((0 + i.val) % 6) := by
  revert i; decide

private theorem l623_blk512_84 (r : Nat) (hlo : 88 ≤ r) (hhi : r < 512) :
    MoonArtifact.commitCode_0_84.get 32 ⟨r, by omega⟩ = l623Word ((43008 + r - 43096) % 6) := by
  have hq : r / 64 < 8 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · omega
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_bnd64_673 ⟨r - 64 - 24, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 64 - 24)) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p4 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 4) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p2 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 2) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p0 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 0) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p4 ⟨r - 320, by omega⟩
    dsimp only at h
    have heq2 : (r - 320 + 4) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p2 ⟨r - 384, by omega⟩
    dsimp only at h
    have heq2 : (r - 384 + 2) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_84
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p0 ⟨r - 448, by omega⟩
    dsimp only at h
    have heq2 : (r - 448 + 0) % 6 = (43008 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

private theorem get_commitCode_to_commitCode_0_85 (idx : Nat) (hlo : 43520 ≤ idx) (hhi : idx < 43887) :
    MoonArtifact.commitCode.get 32 ⟨idx, by omega⟩ =
      MoonArtifact.commitCode_0_85.get 32 ⟨idx - 43520, by omega⟩ := by
  rw [get_commitCode_to_commitCode_1_10 idx (by omega) (by omega)]
  unfold MoonArtifact.commitCode_1_10
  rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
  try exact packed_get_congr _ (by dsimp only; omega)

private theorem l623_bnd64_685 (i : Fin 24) :
    (ArtifactEncoding.Packed.chunk 47 15026279364929135875729658869915608228756423332759603492687791853514047723097552979597435877767143844458887309478125673043389081922279705460792946293397673977163752802902219058181061968868717397482723538206950050571260063964902327720939216811337228647249403873713565344340376118952644102029222473722689306442203559317952099032199358827989112538851995037069692998481737914765793900820864560804669725751556332349994595479926701893974640063253120275).get 32 ⟨0 + i.val, by omega⟩ =
      l623Word ((0 + i.val) % 6) := by
  revert i; decide

private theorem l623_blk512_85 (r : Nat) (hlo : 0 ≤ r) (hhi : r < 344) :
    MoonArtifact.commitCode_0_85.get 32 ⟨r, by omega⟩ = l623Word ((43520 + r - 43096) % 6) := by
  have hq : r / 64 < 6 := by omega
  generalize hqv : r / 64 = q at hq ⊢
  interval_cases q
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p4 ⟨r - 0, by omega⟩
    dsimp only at h
    have heq2 : (r - 0 + 4) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p2 ⟨r - 64, by omega⟩
    dsimp only at h
    have heq2 : (r - 64 + 2) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p0 ⟨r - 128, by omega⟩
    dsimp only at h
    have heq2 : (r - 128 + 0) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p4 ⟨r - 192, by omega⟩
    dsimp only at h
    have heq2 : (r - 192 + 4) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_left _ _ _ _ (by dsimp only; omega)]
    have h := l623_chunk64_p2 ⟨r - 256, by omega⟩
    dsimp only at h
    have heq2 : (r - 256 + 2) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)
  · unfold MoonArtifact.commitCode_0_85
    rw [ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega), ArtifactEncoding.get_join_right _ _ _ _ (by dsimp only; omega)]
    have h := l623_bnd64_685 ⟨r - 320 - 0, by omega⟩
    dsimp only at h
    have heq2 : (0 + (r - 320 - 0)) % 6 = (43520 + r - 43096) % 6 := by omega
    rw [← heq2, ← h]; try exact packed_get_congr _ (by dsimp only; omega)

theorem commit_fetch_l623 (state : MachineState) (k j : Nat) (hk : k < 128) (hj : j < 6)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * (43096 + 6 * k + j))) :
    fetch (submission.image .commit) state = some (l623Instr j) := by
  apply fetch_of_packed_word MoonArtifact.commitCode _ state (43096 + 6 * k + j) (by omega)
    (l623Word j) hpc _ (l623Instr j) (decode_l623Word ⟨j, hj⟩)
  have hb_lo : 84 ≤ (43096 + 6 * k + j) / 512 := by omega
  have hb_hi : (43096 + 6 * k + j) / 512 ≤ 85 := by omega
  generalize hbv : (43096 + 6 * k + j) / 512 = b at hb_lo hb_hi ⊢
  interval_cases b
  · rw [get_commitCode_to_commitCode_0_84 (43096 + 6 * k + j) (by omega) (by omega)]
    rw [l623_blk512_84 (43096 + 6 * k + j - 43008) (by omega) (by omega)]
    exact congrArg l623Word (by omega)
  · rw [get_commitCode_to_commitCode_0_85 (43096 + 6 * k + j) (by omega) (by omega)]
    rw [l623_blk512_85 (43096 + 6 * k + j - 43520) (by omega) (by omega)]
    exact congrArg l623Word (by omega)

/-! ### Commit Program: Non-Parametric Slices -/

def commitPrefixInstr : Nat → Instruction
  | 0 => .base (.ADDI .x8 .x10 (0#12))
  | 1 => .base (.ADDI .x26 .x11 (0#12))
  | 2 => .base (.ADDI .x9 .x12 (0#12))
  | 3 => .base (.ADDI .x6 .x0 (1#12))
  | 4 => .base (.SLLI .x6 .x6 (30#6))
  | 5 => .base (.ADD .x18 .x9 .x6)
  | 6 => .base (.ADDI .x5 .x0 (2#12))
  | 7 => .base (.ADDI .x10 .x18 (40#12))
  | 8 => .base (.ADDI .x11 .x0 (40#12))
  | 9 => .base (.ADDI .x6 .x0 (240#12))
  | 10 => .base (.SLLI .x6 .x6 (11#6))
  | 11 => .base (.SLLI .x6 .x6 (11#6))
  | 12 => .base (.ADDI .x6 .x6 (40#12))
  | 13 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitPrefixInstr_b0 (i : Fin 14) :
    decodeInstruction (MoonArtifact.commitCode_0_0.get 32 ⟨0 + i.val, by omega⟩) =
      some (commitPrefixInstr (0 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitPrefixInstr (state : MachineState) (idx : Nat) (hlo : 0 ≤ idx) (hhi : idx < 14)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitPrefixInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_0 idx (by omega) (by omega)]
  have h := decode_commitPrefixInstr_b0 ⟨idx - 0, by omega⟩
  dsimp only at h
  have heq1 : 0 + (idx - 0) = idx := by omega
  simp only [heq1] at h; exact h

def commitMid0Instr : Nat → Instruction
  | 4110 => .base (.BEQ .x10 .x19 (8#13))
  | 4111 => .base (.JAL .x0 (2080764#21))
  | 4112 => .base (.ADDI .x5 .x0 (0#12))
  | 4113 => .base (.ADDI .x11 .x0 (64#12))
  | 4114 => .base (.ADDI .x13 .x0 (0#12))
  | 4115 => .base (.ADDI .x10 .x8 (4032#12))
  | 4116 => .base (.ADDI .x6 .x0 (1023#12))
  | 4117 => .base (.SLLI .x6 .x6 (11#6))
  | 4118 => .base (.ADDI .x6 .x6 (2047#12))
  | 4119 => .base (.SLLI .x6 .x6 (11#6))
  | 4120 => .base (.ADDI .x6 .x6 (1984#12))
  | 4121 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid0Instr_b8 (i : Fin 12) :
    decodeInstruction (MoonArtifact.commitCode_0_8.get 32 ⟨14 + i.val, by omega⟩) =
      some (commitMid0Instr (4110 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid0Instr (state : MachineState) (idx : Nat) (hlo : 4110 ≤ idx) (hhi : idx < 4122)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid0Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_8 idx (by omega) (by omega)]
  have h := decode_commitMid0Instr_b8 ⟨idx - 4110, by omega⟩
  dsimp only at h
  have heq1 : 14 + (idx - 4110) = idx - 4096 := by omega
  have heq2 : 4110 + (idx - 4110) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1AInstr : Nat → Instruction
  | 10266 => .base (.BEQ .x10 .x19 (8#13))
  | 10267 => .base (.JAL .x0 (2072572#21))
  | 10268 => .base (.ADDI .x11 .x0 (200#12))
  | 10269 => .base (.ADDI .x13 .x0 (1#12))
  | 10270 => .base (.ADDI .x10 .x8 (3864#12))
  | 10271 => .base (.ADDI .x6 .x0 (1023#12))
  | 10272 => .base (.SLLI .x6 .x6 (11#6))
  | 10273 => .base (.ADDI .x6 .x6 (2047#12))
  | 10274 => .base (.SLLI .x6 .x6 (11#6))
  | 10275 => .base (.ADDI .x6 .x6 (1816#12))
  | 10276 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1AInstr_b20 (i : Fin 11) :
    decodeInstruction (MoonArtifact.commitCode_0_20.get 32 ⟨26 + i.val, by omega⟩) =
      some (commitMid1AInstr (10266 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1AInstr (state : MachineState) (idx : Nat) (hlo : 10266 ≤ idx) (hhi : idx < 10277)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1AInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_20 idx (by omega) (by omega)]
  have h := decode_commitMid1AInstr_b20 ⟨idx - 10266, by omega⟩
  dsimp only at h
  have heq1 : 26 + (idx - 10266) = idx - 10240 := by omega
  have heq2 : 10266 + (idx - 10266) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1BInstr : Nat → Instruction
  | 16421 => .base (.BEQ .x10 .x19 (8#13))
  | 16422 => .base (.JAL .x0 (2072572#21))
  | 16423 => .base (.ADDI .x11 .x0 (64#12))
  | 16424 => .base (.ADDI .x13 .x0 (0#12))
  | 16425 => .base (.ADDI .x10 .x8 (3840#12))
  | 16426 => .base (.ADDI .x12 .x18 (4064#12))
  | 16427 => .base (.ADDI .x6 .x0 (1023#12))
  | 16428 => .base (.SLLI .x6 .x6 (11#6))
  | 16429 => .base (.ADDI .x6 .x6 (2047#12))
  | 16430 => .base (.SLLI .x6 .x6 (11#6))
  | 16431 => .base (.ADDI .x6 .x6 (1792#12))
  | 16432 => .base (.ADD .x19 .x8 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1BInstr_b32 (i : Fin 12) :
    decodeInstruction (MoonArtifact.commitCode_0_32.get 32 ⟨37 + i.val, by omega⟩) =
      some (commitMid1BInstr (16421 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1BInstr (state : MachineState) (idx : Nat) (hlo : 16421 ≤ idx) (hhi : idx < 16433)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1BInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_32 idx (by omega) (by omega)]
  have h := decode_commitMid1BInstr_b32 ⟨idx - 16421, by omega⟩
  dsimp only at h
  have heq1 : 37 + (idx - 16421) = idx - 16384 := by omega
  have heq2 : 16421 + (idx - 16421) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1CInstr : Nat → Instruction
  | 22577 => .base (.BEQ .x10 .x19 (8#13))
  | 22578 => .base (.JAL .x0 (2072572#21))
  | 22579 => .base (.ADDI .x10 .x18 (4032#12))
  | 22580 => .base (.ADDI .x6 .x0 (127#12))
  | 22581 => .base (.SLLI .x6 .x6 (11#6))
  | 22582 => .base (.ADDI .x6 .x6 (2047#12))
  | 22583 => .base (.SLLI .x6 .x6 (11#6))
  | 22584 => .base (.ADDI .x6 .x6 (2016#12))
  | 22585 => .base (.ADD .x12 .x9 .x6)
  | 22586 => .base (.ADDI .x6 .x0 (239#12))
  | 22587 => .base (.SLLI .x6 .x6 (11#6))
  | 22588 => .base (.ADDI .x6 .x6 (2047#12))
  | 22589 => .base (.SLLI .x6 .x6 (11#6))
  | 22590 => .base (.ADDI .x6 .x6 (1984#12))
  | 22591 => .base (.ADD .x19 .x18 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1CInstr_b44 (i : Fin 15) :
    decodeInstruction (MoonArtifact.commitCode_0_44.get 32 ⟨49 + i.val, by omega⟩) =
      some (commitMid1CInstr (22577 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1CInstr (state : MachineState) (idx : Nat) (hlo : 22577 ≤ idx) (hhi : idx < 22592)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1CInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_44 idx (by omega) (by omega)]
  have h := decode_commitMid1CInstr_b44 ⟨idx - 22577, by omega⟩
  dsimp only at h
  have heq1 : 49 + (idx - 22577) = idx - 22528 := by omega
  have heq2 : 22577 + (idx - 22577) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMid1DInstr : Nat → Instruction
  | 28736 => .base (.BEQ .x10 .x19 (8#13))
  | 28737 => .base (.JAL .x0 (2072572#21))
  | 28738 => .base (.ADDI .x6 .x0 (1#12))
  | 28739 => .base (.SLLI .x6 .x6 (30#6))
  | 28740 => .base (.ADD .x10 .x9 .x6)
  | 28741 => .base (.ADDI .x6 .x0 (1#12))
  | 28742 => .base (.SLLI .x6 .x6 (29#6))
  | 28743 => .base (.ADD .x12 .x9 .x6)
  | 28744 => .base (.ADDI .x6 .x0 (1#12))
  | 28745 => .base (.SLLI .x6 .x6 (28#6))
  | 28746 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMid1DInstr_b56 (i : Fin 11) :
    decodeInstruction (MoonArtifact.commitCode_0_56.get 32 ⟨64 + i.val, by omega⟩) =
      some (commitMid1DInstr (28736 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMid1DInstr (state : MachineState) (idx : Nat) (hlo : 28736 ≤ idx) (hhi : idx < 28747)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMid1DInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_56 idx (by omega) (by omega)]
  have h := decode_commitMid1DInstr_b56 ⟨idx - 28736, by omega⟩
  dsimp only at h
  have heq1 : 64 + (idx - 28736) = idx - 28672 := by omega
  have heq2 : 28736 + (idx - 28736) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMidL1Instr : Nat → Instruction
  | 34891 => .base (.BEQ .x12 .x19 (8#13))
  | 34892 => .base (.JAL .x0 (2072572#21))
  | 34893 => .base (.ADDI .x6 .x0 (1#12))
  | 34894 => .base (.SLLI .x6 .x6 (24#6))
  | 34895 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMidL1Instr_b68 (i : Fin 5) :
    decodeInstruction (MoonArtifact.commitCode_0_68.get 32 ⟨75 + i.val, by omega⟩) =
      some (commitMidL1Instr (34891 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMidL1Instr (state : MachineState) (idx : Nat) (hlo : 34891 ≤ idx) (hhi : idx < 34896)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMidL1Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_68 idx (by omega) (by omega)]
  have h := decode_commitMidL1Instr_b68 ⟨idx - 34891, by omega⟩
  dsimp only at h
  have heq1 : 75 + (idx - 34891) = idx - 34816 := by omega
  have heq2 : 34891 + (idx - 34891) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitMidL25Instr : Nat → Instruction
  | 43088 => .base (.BEQ .x12 .x19 (8#13))
  | 43089 => .base (.JAL .x0 (2064380#21))
  | 43090 => .base (.ADDI .x27 .x0 (1#12))
  | 43091 => .base (.SLLI .x27 .x27 (46#6))
  | 43092 => .base (.ADDI .x27 .x27 (4095#12))
  | 43093 => .base (.ADDI .x6 .x0 (1#12))
  | 43094 => .base (.SLLI .x6 .x6 (12#6))
  | 43095 => .base (.ADD .x19 .x9 .x6)
  | _ => .base .EBREAK

private theorem decode_commitMidL25Instr_b84 (i : Fin 8) :
    decodeInstruction (MoonArtifact.commitCode_0_84.get 32 ⟨80 + i.val, by omega⟩) =
      some (commitMidL25Instr (43088 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitMidL25Instr (state : MachineState) (idx : Nat) (hlo : 43088 ≤ idx) (hhi : idx < 43096)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitMidL25Instr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_84 idx (by omega) (by omega)]
  have h := decode_commitMidL25Instr_b84 ⟨idx - 43088, by omega⟩
  dsimp only at h
  have heq1 : 80 + (idx - 43088) = idx - 43008 := by omega
  have heq2 : 43088 + (idx - 43088) = idx := by omega
  simp only [heq1, heq2] at h; exact h

def commitTailInstr : Nat → Instruction
  | 43864 => .base (.BNE .x12 .x19 (5120#13))
  | 43865 => .base (.ADDI .x19 .x9 (64#12))
  | 43866 => .base (.ADDI .x10 .x10 (4032#12))
  | 43867 => .base (.ADDI .x12 .x12 (4064#12))
  | 43868 => .base .ECALL
  | 43869 => .base (.LD .x6 .x12 (24#12))
  | 43870 => .base (.AND .x6 .x6 .x27)
  | 43871 => .base (.SD .x12 .x6 (24#12))
  | 43872 => .base (.BNE .x12 .x19 (8168#13))
  | 43873 => .base (.ADDI .x10 .x10 (4032#12))
  | 43874 => .base (.ADDI .x12 .x12 (4064#12))
  | 43875 => .base .ECALL
  | 43876 => .base (.LD .x6 .x12 (0#12))
  | 43877 => .base (.SD .x26 .x6 (0#12))
  | 43878 => .base (.LD .x6 .x12 (8#12))
  | 43879 => .base (.SD .x26 .x6 (8#12))
  | 43880 => .base (.LD .x6 .x12 (16#12))
  | 43881 => .base (.SD .x26 .x6 (16#12))
  | 43882 => .base (.LD .x6 .x12 (24#12))
  | 43883 => .base (.SD .x26 .x6 (24#12))
  | 43884 => .base (.ADDI .x5 .x0 (1#12))
  | 43885 => .base (.ADDI .x10 .x0 (0#12))
  | 43886 => .base .ECALL
  | _ => .base .EBREAK

private theorem decode_commitTailInstr_b85 (i : Fin 23) :
    decodeInstruction (MoonArtifact.commitCode_0_85.get 32 ⟨344 + i.val, by omega⟩) =
      some (commitTailInstr (43864 + i.val)) := by
  revert i; decide

theorem commit_fetch_commitTailInstr (state : MachineState) (idx : Nat) (hlo : 43864 ≤ idx) (hhi : idx < 43887)
    (hpc : state.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    fetch (submission.image .commit) state = some (commitTailInstr idx) := by
  apply fetch_of_packed MoonArtifact.commitCode _ state idx (by omega) hpc _
  rw [get_commitCode_to_commitCode_0_85 idx (by omega) (by omega)]
  have h := decode_commitTailInstr_b85 ⟨idx - 43864, by omega⟩
  dsimp only at h
  have heq1 : 344 + (idx - 43864) = idx - 43520 := by omega
  have heq2 : 43864 + (idx - 43864) = idx := by omega
  simp only [heq1, heq2] at h; exact h

/-! ### Opening Program (235 words) -/

private def openingInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x9 .x12 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x25 .x15 (0#12))
  | 3 => .base (.ADDI .x26 .x15 (0#12))
  | 4 => .base (.ADDI .x27 .x16 (0#12))
  | 5 => .base (.BEQ .x27 .x0 (404#13))
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
  | 21 => .base (.ADDI .x6 .x6 (40#12))
  | 22 => .base (.ADD .x18 .x9 .x6)
  | 23 => .base (.ADDI .x20 .x0 (1#12))
  | 24 => .base (.SLLI .x20 .x20 (24#6))
  | 25 => .base (.ADDI .x21 .x0 (1#12))
  | 26 => .base (.SLLI .x21 .x21 (12#6))
  | 27 => .base (.LD .x8 .x24 (0#12))
  | 28 => .base (.SRLI .x6 .x8 (1#6))
  | 29 => .base (.SLLI .x7 .x6 (7#6))
  | 30 => .base (.SLLI .x10 .x6 (3#6))
  | 31 => .base (.SUB .x7 .x7 .x10)
  | 32 => .base (.ANDI .x6 .x8 (1#12))
  | 33 => .base (.SLLI .x6 .x6 (4#6))
  | 34 => .base (.ADD .x7 .x7 .x6)
  | 35 => .base (.ADD .x10 .x18 .x7)
  | 36 => .base (.JAL .x1 (296#21))
  | 37 => .base (.ADD .x22 .x20 .x8)
  | 38 => .base (.XORI .x6 .x22 (1#12))
  | 39 => .base (.SLLI .x6 .x6 (5#6))
  | 40 => .base (.ADD .x10 .x9 .x6)
  | 41 => .base (.JAL .x1 (356#21))
  | 42 => .base (.SRLI .x22 .x22 (1#6))
  | 43 => .base (.XORI .x6 .x22 (1#12))
  | 44 => .base (.SLLI .x6 .x6 (5#6))
  | 45 => .base (.ADD .x10 .x9 .x6)
  | 46 => .base (.JAL .x1 (336#21))
  | 47 => .base (.SRLI .x22 .x22 (1#6))
  | 48 => .base (.ADDI .x23 .x0 (4#12))
  | 49 => .base (.XORI .x6 .x22 (1#12))
  | 50 => .base (.SLLI .x6 .x6 (5#6))
  | 51 => .base (.ADD .x10 .x9 .x6)
  | 52 => .base (.JAL .x1 (416#21))
  | 53 => .base (.SRLI .x22 .x22 (1#6))
  | 54 => .base (.ADDI .x23 .x23 (4095#12))
  | 55 => .base (.BNE .x23 .x0 (8168#13))
  | 56 => .base (.ADDI .x23 .x0 (10#12))
  | 57 => .base (.XORI .x6 .x22 (1#12))
  | 58 => .base (.SLLI .x6 .x6 (5#6))
  | 59 => .base (.ADD .x10 .x9 .x6)
  | 60 => .base (.JAL .x1 (520#21))
  | 61 => .base (.SRLI .x22 .x22 (1#6))
  | 62 => .base (.ADDI .x23 .x23 (4095#12))
  | 63 => .base (.BNE .x23 .x0 (8168#13))
  | 64 => .base (.ADD .x6 .x21 .x22)
  | 65 => .base (.ADDI .x7 .x0 (1#12))
  | 66 => .base (.SB .x6 .x7 (0#12))
  | 67 => .base (.ADDI .x24 .x24 (8#12))
  | 68 => .base (.ADDI .x27 .x27 (4095#12))
  | 69 => .base (.BNE .x27 .x0 (8024#13))
  | 70 => .base (.ADDI .x23 .x0 (255#12))
  | 71 => .base (.SLLI .x6 .x23 (1#6))
  | 72 => .base (.ADD .x6 .x21 .x6)
  | 73 => .base (.LBU .x7 .x6 (0#12))
  | 74 => .base (.LBU .x8 .x6 (1#12))
  | 75 => .base (.OR .x11 .x7 .x8)
  | 76 => .base (.ADD .x6 .x21 .x23)
  | 77 => .base (.SB .x6 .x11 (0#12))
  | 78 => .base (.BEQ .x7 .x8 (24#13))
  | 79 => .base (.SLLI .x6 .x23 (6#6))
  | 80 => .base (.ADD .x10 .x9 .x6)
  | 81 => .base (.BEQ .x7 .x0 (8#13))
  | 82 => .base (.ADDI .x10 .x10 (32#12))
  | 83 => .base (.JAL .x1 (428#21))
  | 84 => .base (.ADDI .x23 .x23 (4095#12))
  | 85 => .base (.BNE .x23 .x0 (8136#13))
  | 86 => .base (.ADDI .x10 .x25 (0#12))
  | 87 => .base (.BEQ .x13 .x0 (24#13))
  | 88 => .base (.SB .x10 .x12 (0#12))
  | 89 => .base (.ADDI .x10 .x10 (1#12))
  | 90 => .base (.SRLI .x12 .x12 (8#6))
  | 91 => .base (.ADDI .x13 .x13 (4088#12))
  | 92 => .base (.BNE .x13 .x0 (8176#13))
  | 93 => .base (.BEQ .x17 .x0 (12#13))
  | 94 => .base (.SB .x15 .x16 (0#12))
  | 95 => .base (.ADDI .x15 .x15 (1#12))
  | 96 => .base (.BEQ .x15 .x31 (24#13))
  | 97 => .base (.ADDI .x15 .x15 (4095#12))
  | 98 => .base (.LBU .x6 .x15 (0#12))
  | 99 => .base (.SB .x10 .x6 (0#12))
  | _ => .base .EBREAK

private def openingInstr1 : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x10 (1#12))
  | 1 => .base (.BNE .x15 .x31 (8176#13))
  | 2 => .base (.SUB .x11 .x10 .x26)
  | 3 => .base (.ADDI .x5 .x0 (1#12))
  | 4 => .base (.ADDI .x10 .x0 (0#12))
  | 5 => .base .ECALL
  | 6 => .base (.ADDI .x11 .x0 (0#12))
  | 7 => .base (.ADDI .x5 .x0 (1#12))
  | 8 => .base (.ADDI .x10 .x0 (0#12))
  | 9 => .base .ECALL
  | 10 => .base (.LD .x5 .x10 (0#12))
  | 11 => .base (.SLL .x6 .x5 .x13)
  | 12 => .base (.OR .x12 .x12 .x6)
  | 13 => .base (.SD .x25 .x12 (0#12))
  | 14 => .base (.SRLI .x5 .x5 (1#6))
  | 15 => .base (.SRL .x12 .x5 .x14)
  | 16 => .base (.LD .x5 .x10 (8#12))
  | 17 => .base (.SLL .x6 .x5 .x13)
  | 18 => .base (.OR .x12 .x12 .x6)
  | 19 => .base (.SD .x25 .x12 (8#12))
  | 20 => .base (.SRLI .x5 .x5 (1#6))
  | 21 => .base (.SRL .x12 .x5 .x14)
  | 22 => .base (.LD .x5 .x10 (16#12))
  | 23 => .base (.SLL .x6 .x5 .x13)
  | 24 => .base (.OR .x12 .x12 .x6)
  | 25 => .base (.SD .x25 .x12 (16#12))
  | 26 => .base (.SRLI .x5 .x5 (1#6))
  | 27 => .base (.SRL .x12 .x5 .x14)
  | 28 => .base (.ADDI .x25 .x25 (24#12))
  | 29 => .base (.JALR .x0 .x1 (0#12))
  | 30 => .base (.LD .x5 .x10 (0#12))
  | 31 => .base (.SLL .x6 .x5 .x13)
  | 32 => .base (.OR .x12 .x12 .x6)
  | 33 => .base (.SD .x25 .x12 (0#12))
  | 34 => .base (.SRLI .x5 .x5 (1#6))
  | 35 => .base (.SRL .x12 .x5 .x14)
  | 36 => .base (.LD .x5 .x10 (8#12))
  | 37 => .base (.SLL .x6 .x5 .x13)
  | 38 => .base (.OR .x12 .x12 .x6)
  | 39 => .base (.SD .x25 .x12 (8#12))
  | 40 => .base (.SRLI .x5 .x5 (1#6))
  | 41 => .base (.SRL .x12 .x5 .x14)
  | 42 => .base (.LD .x5 .x10 (16#12))
  | 43 => .base (.SLL .x6 .x5 .x13)
  | 44 => .base (.OR .x12 .x12 .x6)
  | 45 => .base (.SD .x25 .x12 (16#12))
  | 46 => .base (.SRLI .x5 .x5 (1#6))
  | 47 => .base (.SRL .x12 .x5 .x14)
  | 48 => .base (.LD .x5 .x10 (24#12))
  | 49 => .base (.SLL .x6 .x5 .x13)
  | 50 => .base (.OR .x12 .x12 .x6)
  | 51 => .base (.SD .x25 .x12 (24#12))
  | 52 => .base (.SRLI .x5 .x5 (1#6))
  | 53 => .base (.SRL .x12 .x5 .x14)
  | 54 => .base (.ADDI .x25 .x25 (32#12))
  | 55 => .base (.JALR .x0 .x1 (0#12))
  | 56 => .base (.LD .x5 .x10 (0#12))
  | 57 => .base (.SLL .x6 .x5 .x13)
  | 58 => .base (.OR .x12 .x12 .x6)
  | 59 => .base (.SD .x25 .x12 (0#12))
  | 60 => .base (.SRLI .x5 .x5 (1#6))
  | 61 => .base (.SRL .x12 .x5 .x14)
  | 62 => .base (.LD .x5 .x10 (8#12))
  | 63 => .base (.SLL .x6 .x5 .x13)
  | 64 => .base (.OR .x12 .x12 .x6)
  | 65 => .base (.SD .x25 .x12 (8#12))
  | 66 => .base (.SRLI .x5 .x5 (1#6))
  | 67 => .base (.SRL .x12 .x5 .x14)
  | 68 => .base (.LD .x5 .x10 (16#12))
  | 69 => .base (.SLL .x6 .x5 .x13)
  | 70 => .base (.OR .x12 .x12 .x6)
  | 71 => .base (.SD .x25 .x12 (16#12))
  | 72 => .base (.SRLI .x5 .x5 (1#6))
  | 73 => .base (.SRL .x12 .x5 .x14)
  | 74 => .base (.ADDI .x25 .x25 (24#12))
  | 75 => .base (.LD .x5 .x10 (24#12))
  | 76 => .base (.SLLI .x5 .x5 (16#6))
  | 77 => .base (.SRLI .x5 .x5 (16#6))
  | 78 => .base (.SLL .x6 .x5 .x13)
  | 79 => .base (.OR .x12 .x12 .x6)
  | 80 => .base (.ADDI .x13 .x13 (48#12))
  | 81 => .base (.ADDI .x7 .x0 (64#12))
  | 82 => .base (.BLTU .x13 .x7 (24#13))
  | 83 => .base (.SD .x25 .x12 (0#12))
  | 84 => .base (.ADDI .x25 .x25 (8#12))
  | 85 => .base (.SRLI .x5 .x5 (1#6))
  | 86 => .base (.SRL .x12 .x5 .x14)
  | 87 => .base (.ADDI .x13 .x13 (4032#12))
  | 88 => .base (.XORI .x14 .x13 (63#12))
  | 89 => .base (.JALR .x0 .x1 (0#12))
  | 90 => .base (.LD .x5 .x10 (0#12))
  | 91 => .base (.SLL .x6 .x5 .x13)
  | 92 => .base (.OR .x12 .x12 .x6)
  | 93 => .base (.SD .x25 .x12 (0#12))
  | 94 => .base (.SRLI .x5 .x5 (1#6))
  | 95 => .base (.SRL .x12 .x5 .x14)
  | 96 => .base (.LD .x5 .x10 (8#12))
  | 97 => .base (.SLL .x6 .x5 .x13)
  | 98 => .base (.OR .x12 .x12 .x6)
  | 99 => .base (.SD .x25 .x12 (8#12))
  | _ => .base .EBREAK

private def openingInstr2 : Nat → Instruction
  | 0 => .base (.SRLI .x5 .x5 (1#6))
  | 1 => .base (.SRL .x12 .x5 .x14)
  | 2 => .base (.LD .x5 .x10 (16#12))
  | 3 => .base (.SLL .x6 .x5 .x13)
  | 4 => .base (.OR .x12 .x12 .x6)
  | 5 => .base (.SD .x25 .x12 (16#12))
  | 6 => .base (.SRLI .x5 .x5 (1#6))
  | 7 => .base (.SRL .x12 .x5 .x14)
  | 8 => .base (.ADDI .x25 .x25 (24#12))
  | 9 => .base (.LD .x11 .x10 (24#12))
  | 10 => .base (.SLLI .x5 .x11 (24#6))
  | 11 => .base (.SRLI .x5 .x5 (24#6))
  | 12 => .base (.SLL .x6 .x5 .x13)
  | 13 => .base (.OR .x12 .x12 .x6)
  | 14 => .base (.ADDI .x13 .x13 (40#12))
  | 15 => .base (.ADDI .x7 .x0 (64#12))
  | 16 => .base (.BLTU .x13 .x7 (24#13))
  | 17 => .base (.SD .x25 .x12 (0#12))
  | 18 => .base (.ADDI .x25 .x25 (8#12))
  | 19 => .base (.SRLI .x5 .x5 (1#6))
  | 20 => .base (.SRL .x12 .x5 .x14)
  | 21 => .base (.ADDI .x13 .x13 (4032#12))
  | 22 => .base (.XORI .x14 .x13 (63#12))
  | 23 => .base (.SRLI .x5 .x11 (40#6))
  | 24 => .base (.ANDI .x5 .x5 (63#12))
  | 25 => .base (.SLL .x6 .x5 .x17)
  | 26 => .base (.OR .x16 .x16 .x6)
  | 27 => .base (.ADDI .x17 .x17 (6#12))
  | 28 => .base (.ADDI .x7 .x0 (8#12))
  | 29 => .base (.BLTU .x17 .x7 (20#13))
  | 30 => .base (.SB .x15 .x16 (0#12))
  | 31 => .base (.ADDI .x15 .x15 (1#12))
  | 32 => .base (.SRLI .x16 .x16 (8#6))
  | 33 => .base (.ADDI .x17 .x17 (4088#12))
  | 34 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def openingInstr (idx : Nat) : Instruction :=
  if idx < 100 then openingInstr0 idx
  else if idx < 200 then openingInstr1 (idx - 100)
  else openingInstr2 (idx - 200)

private theorem decode_opening_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨i.val, by omega⟩) =
      some (openingInstr (i.val)) := by
  revert i; decide

private theorem decode_opening_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (openingInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_opening_2 (i : Fin 35) :
    decodeInstruction (MoonArtifact.openingCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (openingInstr (200 + i.val)) := by
  revert i; decide

theorem opening_fetch (state : MachineState) (idx : Nat) (hhi : idx < 235)
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

/-! ### Check Program (277 words) -/

private def checkInstr0 : Nat → Instruction
  | 0 => .base (.ADDI .x26 .x11 (0#12))
  | 1 => .base (.ADDI .x24 .x13 (0#12))
  | 2 => .base (.ADDI .x8 .x14 (0#12))
  | 3 => .base (.ADDI .x25 .x15 (0#12))
  | 4 => .base (.ADD .x31 .x15 .x17)
  | 5 => .base (.ADDI .x27 .x16 (0#12))
  | 6 => .base (.BNE .x27 .x0 (12#13))
  | 7 => .base (.BNE .x17 .x0 (944#13))
  | 8 => .base (.JAL .x0 (928#21))
  | 9 => .base (.ADDI .x3 .x0 (0#12))
  | 10 => .base (.ADDI .x4 .x0 (0#12))
  | 11 => .base (.ADDI .x9 .x0 (1#12))
  | 12 => .base (.SLLI .x9 .x9 (46#6))
  | 13 => .base (.ADDI .x9 .x9 (4095#12))
  | 14 => .base (.ADDI .x21 .x0 (1#12))
  | 15 => .base (.SLLI .x21 .x21 (12#6))
  | 16 => .base (.ADDI .x18 .x0 (1#12))
  | 17 => .base (.SLLI .x18 .x18 (13#6))
  | 18 => .base (.ADDI .x19 .x0 (1#12))
  | 19 => .base (.SLLI .x19 .x19 (14#6))
  | 20 => .base (.ADDI .x28 .x0 (1#12))
  | 21 => .base (.SLLI .x28 .x28 (24#6))
  | 22 => .base (.ADDI .x5 .x0 (0#12))
  | 23 => .base (.LD .x20 .x24 (0#12))
  | 24 => .base (.ADDI .x6 .x25 (24#12))
  | 25 => .base (.BLTU .x31 .x6 (872#13))
  | 26 => .base (.ADDI .x11 .x0 (64#12))
  | 27 => .base (.ADDI .x13 .x0 (0#12))
  | 28 => .base (.ADDI .x10 .x8 (192#12))
  | 29 => .base (.ADDI .x12 .x10 (0#12))
  | 30 => .base .ECALL
  | 31 => .base (.ADDI .x11 .x0 (200#12))
  | 32 => .base (.ADDI .x13 .x0 (1#12))
  | 33 => .base (.ADDI .x10 .x8 (24#12))
  | 34 => .base (.ADDI .x12 .x10 (0#12))
  | 35 => .base .ECALL
  | 36 => .base (.ADDI .x11 .x0 (64#12))
  | 37 => .base (.ADDI .x13 .x0 (0#12))
  | 38 => .base (.ADDI .x10 .x8 (0#12))
  | 39 => .base (.ANDI .x7 .x20 (1#12))
  | 40 => .base (.SLLI .x7 .x7 (5#6))
  | 41 => .base (.ADD .x12 .x21 .x7)
  | 42 => .base .ECALL
  | 43 => .base (.ANDI .x7 .x20 (1#12))
  | 44 => .base (.BNE .x7 .x0 (24#13))
  | 45 => .base (.SD .x21 .x0 (32#12))
  | 46 => .base (.ADDI .x12 .x21 (40#12))
  | 47 => .base (.ADDI .x10 .x0 (24#12))
  | 48 => .base (.JAL .x1 (792#21))
  | 49 => .base (.JAL .x0 (20#21))
  | 50 => .base (.SD .x21 .x0 (24#12))
  | 51 => .base (.ADDI .x12 .x21 (0#12))
  | 52 => .base (.ADDI .x10 .x0 (24#12))
  | 53 => .base (.JAL .x1 (772#21))
  | 54 => .base (.ADDI .x10 .x21 (0#12))
  | 55 => .base (.ADDI .x12 .x21 (0#12))
  | 56 => .base .ECALL
  | 57 => .base (.ADD .x22 .x28 .x20)
  | 58 => .base (.ADDI .x6 .x25 (32#12))
  | 59 => .base (.BLTU .x31 .x6 (736#13))
  | 60 => .base (.ANDI .x7 .x22 (1#12))
  | 61 => .base (.BEQ .x7 .x0 (52#13))
  | 62 => .base (.LD .x6 .x21 (0#12))
  | 63 => .base (.SD .x21 .x6 (32#12))
  | 64 => .base (.LD .x6 .x21 (8#12))
  | 65 => .base (.SD .x21 .x6 (40#12))
  | 66 => .base (.LD .x6 .x21 (16#12))
  | 67 => .base (.SD .x21 .x6 (48#12))
  | 68 => .base (.LD .x6 .x21 (24#12))
  | 69 => .base (.SD .x21 .x6 (56#12))
  | 70 => .base (.ADDI .x12 .x21 (0#12))
  | 71 => .base (.ADDI .x10 .x0 (32#12))
  | 72 => .base (.JAL .x1 (696#21))
  | 73 => .base (.JAL .x0 (16#21))
  | 74 => .base (.ADDI .x12 .x21 (32#12))
  | 75 => .base (.ADDI .x10 .x0 (32#12))
  | 76 => .base (.JAL .x1 (680#21))
  | 77 => .base (.ADDI .x10 .x21 (0#12))
  | 78 => .base (.ADDI .x12 .x21 (0#12))
  | 79 => .base .ECALL
  | 80 => .base (.SRLI .x22 .x22 (1#6))
  | 81 => .base (.ADDI .x6 .x25 (32#12))
  | 82 => .base (.BLTU .x31 .x6 (644#13))
  | 83 => .base (.ANDI .x7 .x22 (1#12))
  | 84 => .base (.BEQ .x7 .x0 (52#13))
  | 85 => .base (.LD .x6 .x21 (0#12))
  | 86 => .base (.SD .x21 .x6 (32#12))
  | 87 => .base (.LD .x6 .x21 (8#12))
  | 88 => .base (.SD .x21 .x6 (40#12))
  | 89 => .base (.LD .x6 .x21 (16#12))
  | 90 => .base (.SD .x21 .x6 (48#12))
  | 91 => .base (.LD .x6 .x21 (24#12))
  | 92 => .base (.SD .x21 .x6 (56#12))
  | 93 => .base (.ADDI .x12 .x21 (0#12))
  | 94 => .base (.ADDI .x10 .x0 (32#12))
  | 95 => .base (.JAL .x1 (604#21))
  | 96 => .base (.JAL .x0 (16#21))
  | 97 => .base (.ADDI .x12 .x21 (32#12))
  | 98 => .base (.ADDI .x10 .x0 (32#12))
  | 99 => .base (.JAL .x1 (588#21))
  | _ => .base .EBREAK

private def checkInstr1 : Nat → Instruction
  | 0 => .base (.ADDI .x10 .x21 (0#12))
  | 1 => .base (.ADDI .x12 .x21 (0#12))
  | 2 => .base .ECALL
  | 3 => .base (.SH .x21 .x0 (30#12))
  | 4 => .base (.SRLI .x22 .x22 (1#6))
  | 5 => .base (.ADDI .x23 .x0 (4#12))
  | 6 => .base (.ADDI .x6 .x25 (30#12))
  | 7 => .base (.BLTU .x31 .x6 (544#13))
  | 8 => .base (.ANDI .x7 .x22 (1#12))
  | 9 => .base (.BEQ .x7 .x0 (56#13))
  | 10 => .base (.LD .x6 .x21 (0#12))
  | 11 => .base (.SD .x21 .x6 (32#12))
  | 12 => .base (.LD .x6 .x21 (8#12))
  | 13 => .base (.SD .x21 .x6 (40#12))
  | 14 => .base (.LD .x6 .x21 (16#12))
  | 15 => .base (.SD .x21 .x6 (48#12))
  | 16 => .base (.LD .x6 .x21 (24#12))
  | 17 => .base (.SD .x21 .x6 (56#12))
  | 18 => .base (.ADDI .x12 .x21 (0#12))
  | 19 => .base (.ADDI .x10 .x0 (30#12))
  | 20 => .base (.JAL .x1 (504#21))
  | 21 => .base (.SH .x21 .x0 (30#12))
  | 22 => .base (.JAL .x0 (20#21))
  | 23 => .base (.ADDI .x12 .x21 (32#12))
  | 24 => .base (.ADDI .x10 .x0 (30#12))
  | 25 => .base (.JAL .x1 (484#21))
  | 26 => .base (.SH .x21 .x0 (62#12))
  | 27 => .base (.ADDI .x10 .x21 (0#12))
  | 28 => .base (.ADDI .x12 .x21 (0#12))
  | 29 => .base .ECALL
  | 30 => .base (.ADDI .x6 .x0 (1#12))
  | 31 => .base (.BEQ .x23 .x6 (12#13))
  | 32 => .base (.SH .x21 .x0 (30#12))
  | 33 => .base (.JAL .x0 (16#21))
  | 34 => .base (.LD .x6 .x21 (24#12))
  | 35 => .base (.AND .x6 .x6 .x9)
  | 36 => .base (.SD .x21 .x6 (24#12))
  | 37 => .base (.SRLI .x22 .x22 (1#6))
  | 38 => .base (.ADDI .x23 .x23 (4095#12))
  | 39 => .base (.BNE .x23 .x0 (8060#13))
  | 40 => .base (.ADDI .x23 .x0 (10#12))
  | 41 => .base (.ANDI .x7 .x22 (1#12))
  | 42 => .base (.BEQ .x7 .x0 (48#13))
  | 43 => .base (.LD .x6 .x21 (0#12))
  | 44 => .base (.SD .x21 .x6 (32#12))
  | 45 => .base (.LD .x6 .x21 (8#12))
  | 46 => .base (.SD .x21 .x6 (40#12))
  | 47 => .base (.LD .x6 .x21 (16#12))
  | 48 => .base (.SD .x21 .x6 (48#12))
  | 49 => .base (.LD .x6 .x21 (24#12))
  | 50 => .base (.SD .x21 .x6 (56#12))
  | 51 => .base (.ADDI .x12 .x21 (0#12))
  | 52 => .base (.JAL .x1 (404#21))
  | 53 => .base (.JAL .x0 (12#21))
  | 54 => .base (.ADDI .x12 .x21 (32#12))
  | 55 => .base (.JAL .x1 (392#21))
  | 56 => .base (.ADDI .x10 .x21 (0#12))
  | 57 => .base (.ADDI .x12 .x21 (0#12))
  | 58 => .base .ECALL
  | 59 => .base (.LD .x6 .x21 (24#12))
  | 60 => .base (.AND .x6 .x6 .x9)
  | 61 => .base (.SD .x21 .x6 (24#12))
  | 62 => .base (.SRLI .x22 .x22 (1#6))
  | 63 => .base (.ADDI .x23 .x23 (4095#12))
  | 64 => .base (.BNE .x23 .x0 (8100#13))
  | 65 => .base (.SLLI .x6 .x22 (5#6))
  | 66 => .base (.ADD .x14 .x19 .x6)
  | 67 => .base (.ADD .x15 .x18 .x22)
  | 68 => .base (.LBU .x7 .x15 (0#12))
  | 69 => .base (.BNE .x7 .x0 (48#13))
  | 70 => .base (.ADDI .x7 .x0 (1#12))
  | 71 => .base (.SB .x15 .x7 (0#12))
  | 72 => .base (.LD .x6 .x21 (0#12))
  | 73 => .base (.SD .x14 .x6 (0#12))
  | 74 => .base (.LD .x6 .x21 (8#12))
  | 75 => .base (.SD .x14 .x6 (8#12))
  | 76 => .base (.LD .x6 .x21 (16#12))
  | 77 => .base (.SD .x14 .x6 (16#12))
  | 78 => .base (.LD .x6 .x21 (24#12))
  | 79 => .base (.SD .x14 .x6 (24#12))
  | 80 => .base (.JAL .x0 (52#21))
  | 81 => .base (.LD .x6 .x21 (0#12))
  | 82 => .base (.LD .x7 .x14 (0#12))
  | 83 => .base (.BNE .x6 .x7 (240#13))
  | 84 => .base (.LD .x6 .x21 (8#12))
  | 85 => .base (.LD .x7 .x14 (8#12))
  | 86 => .base (.BNE .x6 .x7 (228#13))
  | 87 => .base (.LD .x6 .x21 (16#12))
  | 88 => .base (.LD .x7 .x14 (16#12))
  | 89 => .base (.BNE .x6 .x7 (216#13))
  | 90 => .base (.LD .x6 .x21 (24#12))
  | 91 => .base (.LD .x7 .x14 (24#12))
  | 92 => .base (.BNE .x6 .x7 (204#13))
  | 93 => .base (.ADDI .x24 .x24 (8#12))
  | 94 => .base (.ADDI .x8 .x8 (256#12))
  | 95 => .base (.ADDI .x27 .x27 (4095#12))
  | 96 => .base (.BNE .x27 .x0 (7500#13))
  | 97 => .base (.ADDI .x23 .x0 (255#12))
  | 98 => .base (.SLLI .x6 .x23 (1#6))
  | 99 => .base (.ADD .x6 .x18 .x6)
  | _ => .base .EBREAK

private def checkInstr2 : Nat → Instruction
  | 0 => .base (.LBU .x7 .x6 (0#12))
  | 1 => .base (.LBU .x8 .x6 (1#12))
  | 2 => .base (.OR .x14 .x7 .x8)
  | 3 => .base (.BEQ .x14 .x0 (80#13))
  | 4 => .base (.ADD .x6 .x18 .x23)
  | 5 => .base (.SB .x6 .x14 (0#12))
  | 6 => .base (.SLLI .x6 .x23 (6#6))
  | 7 => .base (.ADD .x10 .x19 .x6)
  | 8 => .base (.BEQ .x7 .x8 (28#13))
  | 9 => .base (.ADDI .x12 .x10 (0#12))
  | 10 => .base (.BEQ .x7 .x0 (8#13))
  | 11 => .base (.ADDI .x12 .x10 (32#12))
  | 12 => .base (.ADDI .x15 .x10 (0#12))
  | 13 => .base (.JAL .x1 (160#21))
  | 14 => .base (.ADDI .x10 .x15 (0#12))
  | 15 => .base (.SLLI .x6 .x23 (5#6))
  | 16 => .base (.ADD .x12 .x19 .x6)
  | 17 => .base .ECALL
  | 18 => .base (.ADDI .x6 .x0 (1#12))
  | 19 => .base (.BEQ .x23 .x6 (16#13))
  | 20 => .base (.LD .x6 .x12 (24#12))
  | 21 => .base (.AND .x6 .x6 .x9)
  | 22 => .base (.SD .x12 .x6 (24#12))
  | 23 => .base (.ADDI .x23 .x23 (4095#12))
  | 24 => .base (.BNE .x23 .x0 (8088#13))
  | 25 => .base (.BNE .x25 .x31 (72#13))
  | 26 => .base (.BNE .x3 .x0 (68#13))
  | 27 => .base (.ADDI .x10 .x19 (32#12))
  | 28 => .base (.LD .x6 .x10 (0#12))
  | 29 => .base (.LD .x7 .x26 (0#12))
  | 30 => .base (.BNE .x6 .x7 (52#13))
  | 31 => .base (.LD .x6 .x10 (8#12))
  | 32 => .base (.LD .x7 .x26 (8#12))
  | 33 => .base (.BNE .x6 .x7 (40#13))
  | 34 => .base (.LD .x6 .x10 (16#12))
  | 35 => .base (.LD .x7 .x26 (16#12))
  | 36 => .base (.BNE .x6 .x7 (28#13))
  | 37 => .base (.LD .x6 .x10 (24#12))
  | 38 => .base (.LD .x7 .x26 (24#12))
  | 39 => .base (.BNE .x6 .x7 (16#13))
  | 40 => .base (.ADDI .x5 .x0 (1#12))
  | 41 => .base (.ADDI .x10 .x0 (0#12))
  | 42 => .base .ECALL
  | 43 => .base (.ADDI .x5 .x0 (1#12))
  | 44 => .base (.ADDI .x10 .x0 (1#12))
  | 45 => .base .ECALL
  | 46 => .base (.LBU .x6 .x25 (0#12))
  | 47 => .base (.SB .x12 .x6 (0#12))
  | 48 => .base (.ADDI .x25 .x25 (1#12))
  | 49 => .base (.ADDI .x12 .x12 (1#12))
  | 50 => .base (.ADDI .x10 .x10 (4095#12))
  | 51 => .base (.BNE .x10 .x0 (8172#13))
  | 52 => .base (.JALR .x0 .x1 (0#12))
  | 53 => .base (.ADDI .x6 .x25 (29#12))
  | 54 => .base (.BLTU .x31 .x6 (8148#13))
  | 55 => .base (.ADDI .x7 .x0 (29#12))
  | 56 => .base (.LBU .x6 .x25 (0#12))
  | 57 => .base (.SB .x12 .x6 (0#12))
  | 58 => .base (.ADDI .x25 .x25 (1#12))
  | 59 => .base (.ADDI .x12 .x12 (1#12))
  | 60 => .base (.ADDI .x7 .x7 (4095#12))
  | 61 => .base (.BNE .x7 .x0 (8172#13))
  | 62 => .base (.ADDI .x7 .x0 (6#12))
  | 63 => .base (.BGEU .x4 .x7 (28#13))
  | 64 => .base (.BGEU .x25 .x31 (8108#13))
  | 65 => .base (.ADDI .x31 .x31 (4095#12))
  | 66 => .base (.LBU .x6 .x31 (0#12))
  | 67 => .base (.SLL .x6 .x6 .x4)
  | 68 => .base (.OR .x3 .x3 .x6)
  | 69 => .base (.ADDI .x4 .x4 (8#12))
  | 70 => .base (.ANDI .x6 .x3 (63#12))
  | 71 => .base (.SRLI .x3 .x3 (6#6))
  | 72 => .base (.ADDI .x4 .x4 (4090#12))
  | 73 => .base (.SB .x12 .x6 (0#12))
  | 74 => .base (.SB .x12 .x0 (1#12))
  | 75 => .base (.SB .x12 .x0 (2#12))
  | 76 => .base (.JALR .x0 .x1 (0#12))
  | _ => .base .EBREAK

def checkInstr (idx : Nat) : Instruction :=
  if idx < 100 then checkInstr0 idx
  else if idx < 200 then checkInstr1 (idx - 100)
  else checkInstr2 (idx - 200)

private theorem decode_check_0 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨i.val, by omega⟩) =
      some (checkInstr (i.val)) := by
  revert i; decide

private theorem decode_check_1 (i : Fin 100) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨100 + i.val, by omega⟩) =
      some (checkInstr (100 + i.val)) := by
  revert i; decide

private theorem decode_check_2 (i : Fin 77) :
    decodeInstruction (MoonArtifact.checkCode.get 32 ⟨200 + i.val, by omega⟩) =
      some (checkInstr (200 + i.val)) := by
  revert i; decide

theorem check_fetch (state : MachineState) (idx : Nat) (hhi : idx < 277)
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
