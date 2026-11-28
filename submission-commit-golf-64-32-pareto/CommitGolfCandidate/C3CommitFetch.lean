import CommitGolfCandidate.TwoPermutationPackedLeafFetch

/-! # The 3c1p commit loop in the delivered image

Word 20 is `jal zero,<12341>`. The loop body occupies words `12341 .. 45155`: an entry of four
words, pass 1 (eight words per leaf, 2,048 leaves), a switch of three words, pass 3 (eight words
per leaf plus `addi s4,a2,32` after every 64th leaf and `add s6,s6,t2` after every 256th), then the
latch at the leader's words 45156 (`beq s4,s5,<45172>`, unchanged) and 45157 (`jal zero,<12341>`).
Every decoded instruction below is checked against the artifact by the kernel. -/
namespace TwoPermutationPrototype.RV64.C3Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def blockStart : Nat := 12341

def p1Index (j : Nat) : Nat := blockStart + 4 + 8 * j
def switchIndex : Nat := blockStart + 16388
def p3Index (j : Nat) : Nat := blockStart + 16391 + 8 * j + j / 64 + j / 256

def wordPC (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * index)

def entryOps : List Instr :=
  [.ADDI .x18 .x10 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x10 .x10 3984]

def p1Ops : List Instr :=
  [.ADDI .x10 .x10 304, .ADDI .x12 .x10 0, .ECALL, .ADDI .x10 .x10 4064, .ADDI .x12 .x10 8, .ECALL,
   .ADDI .x10 .x10 4080, .ECALL]

def switchOps : List Instr := [.ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x10 .x18 0]

def p3Ops (j : Nat) : List Instr :=
  [.SD .x10 .x10 144, .LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2048)), .SD .x10 .x31 152,
   .LD .x31 .x22 (BitVec.ofNat 12 (16 * (j % 256) + 2056)), .SD .x10 .x31 160,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32 * (j % 64))), .ECALL, .ADDI .x10 .x10 256]

def opAt (ops : List Instr) (offset : Nat) : Instr := (ops[offset]?).getD .EBREAK

theorem fetch_word (state : MachineState) (index : Nat) (inCode : index < 262071)
    (pc : state.pc = wordPC index) (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index) = some instruction) :
    fetch packedWideCommitImage state = some (.base instruction) :=
  packed_wide_fetch_decoded state index inCode pc instruction decoded

private def P1TileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 8,
    Manifest.decodeBase (packed_wideCodeWord (p1Index (64 * tile + slot.val) + offset.val)) =
      some (opAt p1Ops offset.val)

private def P3TileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 8,
    Manifest.decodeBase (packed_wideCodeWord (p3Index (64 * tile + slot.val) + offset.val)) =
      some (opAt (p3Ops (64 * tile + slot.val)) offset.val)

private theorem p1_tile0 : P1TileDecodes 0 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile1 : P1TileDecodes 1 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile2 : P1TileDecodes 2 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile3 : P1TileDecodes 3 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile4 : P1TileDecodes 4 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile5 : P1TileDecodes 5 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile6 : P1TileDecodes 6 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile7 : P1TileDecodes 7 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile8 : P1TileDecodes 8 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile9 : P1TileDecodes 9 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile10 : P1TileDecodes 10 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile11 : P1TileDecodes 11 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile12 : P1TileDecodes 12 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile13 : P1TileDecodes 13 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile14 : P1TileDecodes 14 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile15 : P1TileDecodes 15 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile16 : P1TileDecodes 16 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile17 : P1TileDecodes 17 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile18 : P1TileDecodes 18 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile19 : P1TileDecodes 19 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile20 : P1TileDecodes 20 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile21 : P1TileDecodes 21 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile22 : P1TileDecodes 22 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile23 : P1TileDecodes 23 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile24 : P1TileDecodes 24 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile25 : P1TileDecodes 25 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile26 : P1TileDecodes 26 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile27 : P1TileDecodes 27 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile28 : P1TileDecodes 28 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile29 : P1TileDecodes 29 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile30 : P1TileDecodes 30 := by unfold P1TileDecodes; decide +kernel
private theorem p1_tile31 : P1TileDecodes 31 := by unfold P1TileDecodes; decide +kernel

private theorem p3_tile0 : P3TileDecodes 0 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile1 : P3TileDecodes 1 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile2 : P3TileDecodes 2 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile3 : P3TileDecodes 3 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile4 : P3TileDecodes 4 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile5 : P3TileDecodes 5 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile6 : P3TileDecodes 6 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile7 : P3TileDecodes 7 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile8 : P3TileDecodes 8 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile9 : P3TileDecodes 9 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile10 : P3TileDecodes 10 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile11 : P3TileDecodes 11 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile12 : P3TileDecodes 12 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile13 : P3TileDecodes 13 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile14 : P3TileDecodes 14 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile15 : P3TileDecodes 15 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile16 : P3TileDecodes 16 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile17 : P3TileDecodes 17 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile18 : P3TileDecodes 18 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile19 : P3TileDecodes 19 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile20 : P3TileDecodes 20 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile21 : P3TileDecodes 21 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile22 : P3TileDecodes 22 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile23 : P3TileDecodes 23 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile24 : P3TileDecodes 24 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile25 : P3TileDecodes 25 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile26 : P3TileDecodes 26 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile27 : P3TileDecodes 27 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile28 : P3TileDecodes 28 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile29 : P3TileDecodes 29 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile30 : P3TileDecodes 30 := by unfold P3TileDecodes; decide +kernel
private theorem p3_tile31 : P3TileDecodes 31 := by unfold P3TileDecodes; decide +kernel

private theorem p1_tiles (tile : Nat) (bound : tile < 32) : P1TileDecodes tile := by
  interval_cases tile
  exacts [p1_tile0, p1_tile1, p1_tile2, p1_tile3, p1_tile4, p1_tile5, p1_tile6, p1_tile7, p1_tile8,
    p1_tile9, p1_tile10, p1_tile11, p1_tile12, p1_tile13, p1_tile14, p1_tile15, p1_tile16, p1_tile17,
    p1_tile18, p1_tile19, p1_tile20, p1_tile21, p1_tile22, p1_tile23, p1_tile24, p1_tile25, p1_tile26,
    p1_tile27, p1_tile28, p1_tile29, p1_tile30, p1_tile31]

private theorem p3_tiles (tile : Nat) (bound : tile < 32) : P3TileDecodes tile := by
  interval_cases tile
  exacts [p3_tile0, p3_tile1, p3_tile2, p3_tile3, p3_tile4, p3_tile5, p3_tile6, p3_tile7, p3_tile8,
    p3_tile9, p3_tile10, p3_tile11, p3_tile12, p3_tile13, p3_tile14, p3_tile15, p3_tile16, p3_tile17,
    p3_tile18, p3_tile19, p3_tile20, p3_tile21, p3_tile22, p3_tile23, p3_tile24, p3_tile25, p3_tile26,
    p3_tile27, p3_tile28, p3_tile29, p3_tile30, p3_tile31]

theorem fetch_p1 (j : Nat) (bound : j < 2048) (offset : Nat) (inside : offset < 8) (state : MachineState)
    (pc : state.pc = wordPC (p1Index j + offset)) :
    fetch packedWideCommitImage state = some (.base (opAt p1Ops offset)) := by
  have tile := p1_tiles (j / 64) (by omega) ⟨j % 64, by omega⟩ ⟨offset, inside⟩
  have pos : 64 * (j / 64) + j % 64 = j := by omega
  simp only [Fin.val_mk, pos] at tile
  exact fetch_word state _ (by unfold p1Index blockStart; omega) pc _ tile

theorem fetch_p3 (j : Nat) (bound : j < 2048) (offset : Nat) (inside : offset < 8) (state : MachineState)
    (pc : state.pc = wordPC (p3Index j + offset)) :
    fetch packedWideCommitImage state = some (.base (opAt (p3Ops j) offset)) := by
  have tile := p3_tiles (j / 64) (by omega) ⟨j % 64, by omega⟩ ⟨offset, inside⟩
  have pos : 64 * (j / 64) + j % 64 = j := by omega
  simp only [Fin.val_mk, pos] at tile
  exact fetch_word state _ (by unfold p3Index blockStart; omega) pc _ tile

private theorem entry_decoded : ∀ i : Fin 4,
    Manifest.decodeBase (packed_wideCodeWord (blockStart + i.val)) = some (opAt entryOps i.val) := by
  decide +kernel

private theorem switch_decoded : ∀ i : Fin 3,
    Manifest.decodeBase (packed_wideCodeWord (switchIndex + i.val)) = some (opAt switchOps i.val) := by
  decide +kernel

theorem fetch_entry (i : Nat) (inside : i < 4) (state : MachineState) (pc : state.pc = wordPC (blockStart + i)) :
    fetch packedWideCommitImage state = some (.base (opAt entryOps i)) :=
  fetch_word state _ (by unfold blockStart; omega) pc _ (entry_decoded ⟨i, inside⟩)

theorem fetch_switch (i : Nat) (inside : i < 3) (state : MachineState) (pc : state.pc = wordPC (switchIndex + i)) :
    fetch packedWideCommitImage state = some (.base (opAt switchOps i)) :=
  fetch_word state _ (by unfold switchIndex blockStart; omega) pc _ (switch_decoded ⟨i, inside⟩)

private theorem heap_rebase_decoded : ∀ tile : Fin 32,
    Manifest.decodeBase (packed_wideCodeWord (p3Index (64 * tile.val + 63) + 8)) = some (.ADDI .x20 .x12 32) := by
  decide +kernel

private theorem nonce_rebase_decoded : ∀ segment : Fin 8,
    Manifest.decodeBase (packed_wideCodeWord (p3Index (256 * segment.val + 255) + 9)) =
      some (.ADD .x22 .x22 .x7) := by
  decide +kernel

theorem fetch_heap_rebase (j : Nat) (bound : j < 2048) (last : j % 64 = 63) (state : MachineState)
    (pc : state.pc = wordPC (p3Index j + 8)) :
    fetch packedWideCommitImage state = some (.base (.ADDI .x20 .x12 32)) := by
  have decoded := heap_rebase_decoded ⟨j / 64, by omega⟩
  have pos : 64 * (j / 64) + 63 = j := by omega
  simp only [Fin.val_mk, pos] at decoded
  exact fetch_word state _ (by unfold p3Index blockStart; omega) pc _ decoded

theorem fetch_nonce_rebase (j : Nat) (bound : j < 2048) (last : j % 256 = 255) (state : MachineState)
    (pc : state.pc = wordPC (p3Index j + 9)) :
    fetch packedWideCommitImage state = some (.base (.ADD .x22 .x22 .x7)) := by
  have decoded := nonce_rebase_decoded ⟨j / 256, by omega⟩
  have pos : 256 * (j / 256) + 255 = j := by omega
  simp only [Fin.val_mk, pos] at decoded
  exact fetch_word state _ (by unfold p3Index blockStart; omega) pc _ decoded

theorem fetch_first_jump (state : MachineState) (pc : state.pc = 4176) :
    fetch packedWideCommitImage state = some (.base (.JAL .x0 49284)) :=
  fetch_word state 20 (by decide) pc _ rfl

theorem fetch_loop_jump (state : MachineState) (pc : state.pc = 184724) :
    fetch packedWideCommitImage state = some (.base (.JAL .x0 1965888)) :=
  fetch_word state 45157 (by decide) pc _ rfl

theorem p3_end : p3Index 2048 = 45156 := by decide

end TwoPermutationPrototype.RV64.C3Leaves
