import CommitGolfCandidate.StreamingLeaf
import CommitGolfCandidate.Group341Encoding

/-! Instruction fetches of the unrolled leaf group. Word 54 calls the appended group at
word 251827 (PC 1011404). Leaf `u < 64` of the group occupies words `251827+31u+i`, `i < 31`:
the 31-instruction leaf body of words 90..120 with the nonce offset `24u` folded into its three
loads and the heap offset `32u` into its last-block address. The group latch follows at words
253811..253816. -/
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

/-- The appended group, word by word, decodes to the relocated leaf bodies. -/
theorem t1_group_leaf_word (u i : Nat) (hu : u < 64) (hi : i < 31) :
    (t1GroupWords[31 * u + i]?).bind decodeInstruction = some (.base (t1LeafInstr u i)) := by
  interval_cases u <;> interval_cases i <;> rfl

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
    (bounded : k < 1990)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (251827 + k)))
    (decoded : (t1GroupWords[k]?).bind decodeInstruction = some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  apply commit_fetch state (251827 + k) _ (by omega) pc
  change (group341ImageWords[251827 + k]?).bind decodeInstruction = _
  rw [t1_group_word]
  exact decoded

/-- Group latch word 0 (PC 1019340): advance the nonce cursor past 64 leaves. -/
theorem t1_image_nonce_step (state : MachineState) (pc : state.pc = 1019340) :
    fetch (submission.image .commit) state = some (.base (.ADDI .x18 .x18 1536)) :=
  t1_image_latch_word 1984 _ state (by decide) pc rfl

/-- Group latch word 1 (PC 1019344): first half of the heap advance. -/
theorem t1_image_heap_step (state : MachineState) (pc : state.pc = 1019344) :
    fetch (submission.image .commit) state = some (.base (.ADDI .x23 .x23 1024)) :=
  t1_image_latch_word 1985 _ state (by decide) pc rfl

/-- Group latch word 2 (PC 1019348): second half of the heap advance. -/
theorem t1_image_heap_step2 (state : MachineState) (pc : state.pc = 1019348) :
    fetch (submission.image .commit) state = some (.base (.ADDI .x23 .x23 1024)) :=
  t1_image_latch_word 1986 _ state (by decide) pc rfl

/-- Group latch word 3 (PC 1019352): `bltu x23, x22, +8` to the re-entry jump. -/
theorem t1_image_group_branch (state : MachineState) (pc : state.pc = 1019352) :
    fetch (submission.image .commit) state = some (.base (.BLTU .x23 .x22 8)) :=
  t1_image_latch_word 1987 _ state (by decide) pc rfl

/-- Group latch word 4 (PC 1019356): `jal x0` to word 67 (PC 4364), the old leaf-loop exit. -/
theorem t1_image_group_exit (state : MachineState) (pc : state.pc = 1019356) :
    fetch (submission.image .commit) state = some (.base (.JAL .x0 1082160)) :=
  t1_image_latch_word 1988 _ state (by decide) pc rfl

/-- Group latch word 5 (PC 1019360): `jal x0` back to the group start (PC 1011404). -/
theorem t1_image_group_loop (state : MachineState) (pc : state.pc = 1019360) :
    fetch (submission.image .commit) state = some (.base (.JAL .x0 2089196)) :=
  t1_image_latch_word 1989 _ state (by decide) pc rfl

/-- The relocated leaf agrees with the base body away from the four relocated slots. -/
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
