import CommitGolfCandidate.WideLeafLatch
import CommitGolfCandidate.StreamingLeaf
import CommitGolfCandidate.Group341Encoding

/-! Instruction fetches of the unrolled leaf group. Word 54 calls the appended group at
word 251827 (PC 1011404). Leaf `u < 64` of the group occupies words `251827+31u+i`, `i < 31`:
the 31-instruction leaf body of words 90..120 with the nonce offset `24u` folded into its three
loads and the heap offset `32u` into its last-block address. The group latch follows at words
253811..253815. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- The original 31-instruction leaf body, words 90..120 (PCs 4456..4576). -/
def t1BaseLeafInstr (i : Nat) : Instr :=
  if i = 0 then .LD .x6 .x18 0 else
  if i = 1 then .SD .x10 .x6 0 else
  if i = 2 then .LD .x6 .x18 8 else
  if i = 3 then .SD .x10 .x6 8 else
  if i = 4 then .LD .x6 .x18 16 else
  if i = 5 then .SD .x10 .x6 16 else
  if i = 6 then .SD .x10 .x0 24 else
  if i = 7 then .ADDI .x12 .x10 32 else
  if i = 28 then .ADDI .x12 .x23 0 else
  if i = 30 then .ADDI .x10 .x10 32 else
  if (i - 8) % 3 = 0 then .ECALL else
  if (i - 8) % 3 = 1 then .ADDI .x10 .x10 32 else
  .ADDI .x12 .x10 32

/-- Leaf `u` of the group: the base body with `24u` and `32u` folded into the immediates. -/
def t1LeafInstr (u i : Nat) : Instr :=
  if i = 0 then .LD .x6 .x18 (BitVec.ofNat 12 (24 * u)) else
  if i = 2 then .LD .x6 .x18 (BitVec.ofNat 12 (24 * u + 8)) else
  if i = 4 then .LD .x6 .x18 (BitVec.ofNat 12 (24 * u + 16)) else
  if i = 28 then .ADDI .x12 .x23 (BitVec.ofNat 12 (32 * u)) else
  t1BaseLeafInstr i

private theorem wide_leaf_decodes_0 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 0 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 0 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_1 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 1 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 1 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_2 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 2 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 2 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_3 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 3 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 3 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_4 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 4 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 4 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_5 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 5 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 5 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_6 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 6 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 6 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_7 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 7 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 7 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_8 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 8 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 8 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_9 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 9 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 9 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_10 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 10 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 10 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_11 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 11 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 11 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_12 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 12 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 12 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_13 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 13 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 13 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_14 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 14 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 14 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_15 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 15 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 15 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_16 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 16 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 16 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_17 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 17 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 17 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_18 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 18 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 18 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_19 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 19 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 19 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_20 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 20 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 20 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_21 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 21 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 21 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_22 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 22 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 22 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_23 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 23 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 23 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_24 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 24 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 24 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_25 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 25 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 25 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_26 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 26 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 26 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_27 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 27 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 27 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_28 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 28 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 28 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_29 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 29 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 29 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_30 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 30 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 30 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_31 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 31 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 31 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_32 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 32 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 32 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_33 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 33 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 33 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_34 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 34 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 34 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_35 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 35 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 35 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_36 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 36 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 36 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_37 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 37 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 37 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_38 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 38 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 38 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_39 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 39 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 39 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_40 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 40 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 40 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_41 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 41 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 41 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_42 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 42 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 42 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_43 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 43 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 43 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_44 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 44 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 44 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_45 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 45 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 45 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_46 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 46 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 46 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_47 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 47 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 47 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_48 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 48 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 48 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_49 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 49 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 49 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_50 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 50 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 50 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_51 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 51 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 51 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_52 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 52 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 52 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_53 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 53 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 53 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_54 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 54 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 54 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_55 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 55 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 55 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_56 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 56 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 56 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_57 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 57 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 57 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_58 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 58 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 58 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_59 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 59 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 59 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_60 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 60 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 60 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_61 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 61 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 61 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_62 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 62 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 62 i)) := by
  interval_cases i <;> rfl

private theorem wide_leaf_decodes_63 (i : Nat) (hi : i < 31) :
    (t1GroupWords[31 * 63 + i]?).bind decodeInstruction = some (.base (t1LeafInstr 63 i)) := by
  interval_cases i <;> rfl

/-- Each fixed leaf is checked separately to bound elaboration memory. -/
theorem t1_group_leaf_word (u i : Nat) (hu : u < 64) (hi : i < 31) :
    (t1GroupWords[31 * u + i]?).bind decodeInstruction = some (.base (t1LeafInstr u i)) := by
  interval_cases u
  · exact wide_leaf_decodes_0 i hi
  · exact wide_leaf_decodes_1 i hi
  · exact wide_leaf_decodes_2 i hi
  · exact wide_leaf_decodes_3 i hi
  · exact wide_leaf_decodes_4 i hi
  · exact wide_leaf_decodes_5 i hi
  · exact wide_leaf_decodes_6 i hi
  · exact wide_leaf_decodes_7 i hi
  · exact wide_leaf_decodes_8 i hi
  · exact wide_leaf_decodes_9 i hi
  · exact wide_leaf_decodes_10 i hi
  · exact wide_leaf_decodes_11 i hi
  · exact wide_leaf_decodes_12 i hi
  · exact wide_leaf_decodes_13 i hi
  · exact wide_leaf_decodes_14 i hi
  · exact wide_leaf_decodes_15 i hi
  · exact wide_leaf_decodes_16 i hi
  · exact wide_leaf_decodes_17 i hi
  · exact wide_leaf_decodes_18 i hi
  · exact wide_leaf_decodes_19 i hi
  · exact wide_leaf_decodes_20 i hi
  · exact wide_leaf_decodes_21 i hi
  · exact wide_leaf_decodes_22 i hi
  · exact wide_leaf_decodes_23 i hi
  · exact wide_leaf_decodes_24 i hi
  · exact wide_leaf_decodes_25 i hi
  · exact wide_leaf_decodes_26 i hi
  · exact wide_leaf_decodes_27 i hi
  · exact wide_leaf_decodes_28 i hi
  · exact wide_leaf_decodes_29 i hi
  · exact wide_leaf_decodes_30 i hi
  · exact wide_leaf_decodes_31 i hi
  · exact wide_leaf_decodes_32 i hi
  · exact wide_leaf_decodes_33 i hi
  · exact wide_leaf_decodes_34 i hi
  · exact wide_leaf_decodes_35 i hi
  · exact wide_leaf_decodes_36 i hi
  · exact wide_leaf_decodes_37 i hi
  · exact wide_leaf_decodes_38 i hi
  · exact wide_leaf_decodes_39 i hi
  · exact wide_leaf_decodes_40 i hi
  · exact wide_leaf_decodes_41 i hi
  · exact wide_leaf_decodes_42 i hi
  · exact wide_leaf_decodes_43 i hi
  · exact wide_leaf_decodes_44 i hi
  · exact wide_leaf_decodes_45 i hi
  · exact wide_leaf_decodes_46 i hi
  · exact wide_leaf_decodes_47 i hi
  · exact wide_leaf_decodes_48 i hi
  · exact wide_leaf_decodes_49 i hi
  · exact wide_leaf_decodes_50 i hi
  · exact wide_leaf_decodes_51 i hi
  · exact wide_leaf_decodes_52 i hi
  · exact wide_leaf_decodes_53 i hi
  · exact wide_leaf_decodes_54 i hi
  · exact wide_leaf_decodes_55 i hi
  · exact wide_leaf_decodes_56 i hi
  · exact wide_leaf_decodes_57 i hi
  · exact wide_leaf_decodes_58 i hi
  · exact wide_leaf_decodes_59 i hi
  · exact wide_leaf_decodes_60 i hi
  · exact wide_leaf_decodes_61 i hi
  · exact wide_leaf_decodes_62 i hi
  · exact wide_leaf_decodes_63 i hi

/-- Word 54 now calls the appended group. -/
theorem t1_image_call (state : MachineState) (pc : state.pc = 4312) :
    fetch (submission.image .commit) state = some (.base (.JAL .x1 1007092)) := by
  apply commit_fetch state 54 _ (by decide) pc
  rfl

/-- Leaf `u`, instruction `i` of the group, at PC `1011404 + 124u + 4i`. -/
theorem t1_image_leaf (u i : Nat) (hu : u < 64) (hi : i < 31) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1011404 + 124 * u + 4 * i)) :
    fetch (submission.image .commit) state = some (.base (t1LeafInstr u i)) := by
  apply commit_fetch state (251827 + (31 * u + i)) _ (by omega)
  · rw [pc]
    congr 1
    omega
  · change (group341ImageWords[251827 + (31 * u + i)]?).bind decodeInstruction = _
    rw [t1_group_word]
    exact t1_group_leaf_word u i hu hi

private theorem t1_image_latch_word (k : Nat) (instruction : Instr) (state : MachineState)
    (bounded : k < 1989)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (251827 + k)))
    (decoded : (t1GroupWords[k]?).bind decodeInstruction = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply commit_fetch state (251827 + k) _ (by omega) pc
  change (group341ImageWords[251827 + k]?).bind decodeInstruction = _
  rw [t1_group_word]
  exact decoded

theorem t1_wide_latch :
    WideLeafFetched (submission.image .commit) 1019340 2089200 1082164 := by
  intro s
  exact ⟨fun h => t1_image_latch_word 1984 _ s (by decide) h rfl,
    fun h => t1_image_latch_word 1985 _ s (by decide) h rfl,
    fun h => t1_image_latch_word 1986 _ s (by decide) h rfl,
    fun h => t1_image_latch_word 1987 _ s (by decide) h rfl,
    fun h => t1_image_latch_word 1988 _ s (by decide) h rfl⟩

theorem t1_leaf_instr_base (u i : Nat) (h0 : i ≠ 0) (h2 : i ≠ 2) (h4 : i ≠ 4) (h28 : i ≠ 28) :
    t1LeafInstr u i = t1BaseLeafInstr i := by
  simp [t1LeafInstr, h0, h2, h4, h28]

/-- Leaf 0 of the group is the base body. -/
theorem t1_leaf_instr_zero (i : Nat) : t1LeafInstr 0 i = t1BaseLeafInstr i := by
  unfold t1LeafInstr
  by_cases h0 : i = 0
  · subst h0; rfl
  by_cases h2 : i = 2
  · subst h2; rfl
  by_cases h4 : i = 4
  · subst h4; rfl
  by_cases h28 : i = 28
  · subst h28; rfl
  simp [h0, h2, h4, h28]

/-- The original leaf body (dead code after the call moved) still decodes at words 90..120. -/
theorem t1_image_base_leaf (i : Nat) (hi : i < 31) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4456 + 4 * i)) :
    fetch (submission.image .commit) state = some (.base (t1BaseLeafInstr i)) := by
  apply commit_fetch state (90 + i) _ (by omega)
  · rw [pc]
    congr 1
    omega
  · interval_cases i <;> rfl

end CommitGolfCandidate
