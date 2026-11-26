import CommitGolfCandidate.TwoPermutationPackedLeafFetch

/-! # The paired commit loop in the delivered image

Words 0..19 are the setup (`s0 = a1 ; s1 = a2 ; s3 = 2^29 ; s4 = s1 + s3 - 32 ; t1 = 200 << 24 ;
s5 = s4 + t1` and twelve NOPs), word 20 is `jal zero,<18517>`. A block (2,048 leaves, 1,024 pairs) is
the prologue (18517..18521), pass 1 (16 words per pair at 18522), the pass-2 setup (34906..34908),
pass 2 (2 words per pair at 34909), the pass-3 setup (36957..36961), pass 3 (8 words per pair at
36962) and the epilogue (45154, 45155); then the latch `beq s4,s5,<45172>` (45156) and
`jal zero,<18517>` (45157). The exit (45172..45177) sets up parent loop 1 and jumps to 53369.
Every decoded instruction below is checked against the artifact by the kernel. -/
namespace TwoPermutationPrototype.RV64.C3P
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def cpc (index : Nat) : Word := BitVec.ofNat 64 (4096 + 4 * index)

def blockStart : Nat := 18517
def p1Index (p : Nat) : Nat := 18522 + 16 * p
def p2Setup : Nat := 34906
def p2Index (p : Nat) : Nat := 34909 + 2 * p
def p3Setup : Nat := 36957
def p3Index (p : Nat) : Nat := 36962 + 8 * p
def epilogue : Nat := 45154

def setupOps : List Instr :=
  [.ADDI .x8 .x11 0, .ADDI .x9 .x12 0, .LUI .x19 0x20000, .ADD .x20 .x9 .x19, .ADDI .x20 .x20 4064,
   .ADDI .x6 .x0 200, .SLLI .x6 .x6 24, .ADD .x21 .x20 .x6,
   .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0,
   .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .ADDI .x0 .x0 0]

def prologueOps : List Instr :=
  [.ADDI .x18 .x10 0, .ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x10 .x10 3840]

def p1Ops : List Instr :=
  [.ADDI .x10 .x10 448, .ADDI .x12 .x10 32, .ECALL, .ADDI .x10 .x10 3904, .ADDI .x12 .x10 192, .ECALL,
   .ADDI .x10 .x10 192, .ECALL, .ADDI .x10 .x10 64, .ADDI .x12 .x10 0, .ECALL,
   .ADDI .x10 .x10 192, .ADDI .x12 .x10 3936, .ECALL, .ADDI .x10 .x10 3904, .ECALL]

def p2SetupOps : List Instr := [.ADDI .x5 .x0 2, .ADDI .x11 .x0 32, .ADDI .x10 .x18 3824]

def p2Ops : List Instr := [.ADDI .x10 .x10 512, .ECALL]

def p3SetupOps : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 200, .ADDI .x13 .x0 1, .ADDI .x10 .x18 3840, .ADDI .x12 .x20 0]

def p3Ops : List Instr :=
  [.ADDI .x10 .x10 312, .SD .x10 .x10 168, .ADDI .x12 .x12 200, .ECALL,
   .ADDI .x10 .x10 200, .SD .x10 .x10 16, .ADDI .x12 .x12 200, .ECALL]

def epilogueOps : List Instr := [.ADDI .x20 .x12 0, .ADDI .x10 .x10 256]

def exitOps : List Instr :=
  [.ADDI .x10 .x21 4064, .ADD .x12 .x9 .x19, .ADDI .x12 .x12 4064, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

def opAt (ops : List Instr) (offset : Nat) : Instr := (ops[offset]?).getD .EBREAK

theorem fetch_word (state : MachineState) (index : Nat) (inCode : index < 262071)
    (pc : state.pc = cpc index) (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index) = some instruction) :
    fetch packedWideCommitImage state = some (.base instruction) :=
  packed_wide_fetch_decoded state index inCode pc instruction decoded

private def P1TileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 32, ∀ offset : Fin 16,
    Manifest.decodeBase (packed_wideCodeWord (p1Index (32 * tile + slot.val) + offset.val)) =
      some (opAt p1Ops offset.val)

private def P2TileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 256, ∀ offset : Fin 2,
    Manifest.decodeBase (packed_wideCodeWord (p2Index (256 * tile + slot.val) + offset.val)) =
      some (opAt p2Ops offset.val)

private def P3TileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 8,
    Manifest.decodeBase (packed_wideCodeWord (p3Index (64 * tile + slot.val) + offset.val)) =
      some (opAt p3Ops offset.val)

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
private theorem p2_tile0 : P2TileDecodes 0 := by unfold P2TileDecodes; decide +kernel
private theorem p2_tile1 : P2TileDecodes 1 := by unfold P2TileDecodes; decide +kernel
private theorem p2_tile2 : P2TileDecodes 2 := by unfold P2TileDecodes; decide +kernel
private theorem p2_tile3 : P2TileDecodes 3 := by unfold P2TileDecodes; decide +kernel
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

private theorem p1_tiles (tile : Nat) (bound : tile < 32) : P1TileDecodes tile := by
  interval_cases tile
  exacts [p1_tile0, p1_tile1, p1_tile2, p1_tile3, p1_tile4, p1_tile5, p1_tile6, p1_tile7, p1_tile8, p1_tile9, p1_tile10, p1_tile11, p1_tile12, p1_tile13, p1_tile14, p1_tile15, p1_tile16, p1_tile17, p1_tile18, p1_tile19, p1_tile20, p1_tile21, p1_tile22, p1_tile23, p1_tile24, p1_tile25, p1_tile26, p1_tile27, p1_tile28, p1_tile29, p1_tile30, p1_tile31]

private theorem p2_tiles (tile : Nat) (bound : tile < 4) : P2TileDecodes tile := by
  interval_cases tile
  exacts [p2_tile0, p2_tile1, p2_tile2, p2_tile3]

private theorem p3_tiles (tile : Nat) (bound : tile < 16) : P3TileDecodes tile := by
  interval_cases tile
  exacts [p3_tile0, p3_tile1, p3_tile2, p3_tile3, p3_tile4, p3_tile5, p3_tile6, p3_tile7, p3_tile8, p3_tile9, p3_tile10, p3_tile11, p3_tile12, p3_tile13, p3_tile14, p3_tile15]

theorem fetch_p1 (p : Nat) (bound : p < 1024) (offset : Nat) (inside : offset < 16) (state : MachineState)
    (pc : state.pc = cpc (p1Index p + offset)) :
    fetch packedWideCommitImage state = some (.base (opAt p1Ops offset)) := by
  have tile := p1_tiles (p / 32) (by omega) ⟨p % 32, by omega⟩ ⟨offset, inside⟩
  have pos : 32 * (p / 32) + p % 32 = p := by omega
  simp only [Fin.val_mk, pos] at tile
  exact fetch_word state _ (by unfold p1Index; omega) pc _ tile

theorem fetch_p2 (p : Nat) (bound : p < 1024) (offset : Nat) (inside : offset < 2) (state : MachineState)
    (pc : state.pc = cpc (p2Index p + offset)) :
    fetch packedWideCommitImage state = some (.base (opAt p2Ops offset)) := by
  have tile := p2_tiles (p / 256) (by omega) ⟨p % 256, by omega⟩ ⟨offset, inside⟩
  have pos : 256 * (p / 256) + p % 256 = p := by omega
  simp only [Fin.val_mk, pos] at tile
  exact fetch_word state _ (by unfold p2Index; omega) pc _ tile

theorem fetch_p3 (p : Nat) (bound : p < 1024) (offset : Nat) (inside : offset < 8) (state : MachineState)
    (pc : state.pc = cpc (p3Index p + offset)) :
    fetch packedWideCommitImage state = some (.base (opAt p3Ops offset)) := by
  have tile := p3_tiles (p / 64) (by omega) ⟨p % 64, by omega⟩ ⟨offset, inside⟩
  have pos : 64 * (p / 64) + p % 64 = p := by omega
  simp only [Fin.val_mk, pos] at tile
  exact fetch_word state _ (by unfold p3Index; omega) pc _ tile

private theorem setup_decoded : ∀ i : Fin 20,
    Manifest.decodeBase (packed_wideCodeWord i.val) = some (opAt setupOps i.val) := by decide +kernel
private theorem prologue_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (blockStart + i.val)) = some (opAt prologueOps i.val) := by
  decide +kernel
private theorem p2_setup_decoded : ∀ i : Fin 3,
    Manifest.decodeBase (packed_wideCodeWord (p2Setup + i.val)) = some (opAt p2SetupOps i.val) := by
  decide +kernel
private theorem p3_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (p3Setup + i.val)) = some (opAt p3SetupOps i.val) := by
  decide +kernel
private theorem epilogue_decoded : ∀ i : Fin 2,
    Manifest.decodeBase (packed_wideCodeWord (epilogue + i.val)) = some (opAt epilogueOps i.val) := by
  decide +kernel
private theorem exit_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (45172 + i.val)) = some (opAt exitOps i.val) := by
  decide +kernel

theorem fetch_setup (i : Nat) (inside : i < 20) (state : MachineState) (pc : state.pc = cpc i) :
    fetch packedWideCommitImage state = some (.base (opAt setupOps i)) :=
  fetch_word state _ (by omega) pc _ (setup_decoded ⟨i, inside⟩)

theorem fetch_prologue (i : Nat) (inside : i < 5) (state : MachineState) (pc : state.pc = cpc (blockStart + i)) :
    fetch packedWideCommitImage state = some (.base (opAt prologueOps i)) :=
  fetch_word state _ (by unfold blockStart; omega) pc _ (prologue_decoded ⟨i, inside⟩)

theorem fetch_p2_setup (i : Nat) (inside : i < 3) (state : MachineState) (pc : state.pc = cpc (p2Setup + i)) :
    fetch packedWideCommitImage state = some (.base (opAt p2SetupOps i)) :=
  fetch_word state _ (by unfold p2Setup; omega) pc _ (p2_setup_decoded ⟨i, inside⟩)

theorem fetch_p3_setup (i : Nat) (inside : i < 5) (state : MachineState) (pc : state.pc = cpc (p3Setup + i)) :
    fetch packedWideCommitImage state = some (.base (opAt p3SetupOps i)) :=
  fetch_word state _ (by unfold p3Setup; omega) pc _ (p3_setup_decoded ⟨i, inside⟩)

theorem fetch_epilogue (i : Nat) (inside : i < 2) (state : MachineState) (pc : state.pc = cpc (epilogue + i)) :
    fetch packedWideCommitImage state = some (.base (opAt epilogueOps i)) :=
  fetch_word state _ (by unfold epilogue; omega) pc _ (epilogue_decoded ⟨i, inside⟩)

theorem fetch_exit (i : Nat) (inside : i < 5) (state : MachineState) (pc : state.pc = cpc (45172 + i)) :
    fetch packedWideCommitImage state = some (.base (opAt exitOps i)) :=
  fetch_word state _ (by omega) pc _ (exit_decoded ⟨i, inside⟩)

theorem fetch_first_jump (state : MachineState) (pc : state.pc = cpc 20) :
    fetch packedWideCommitImage state = some (.base (.JAL .x0 73988)) :=
  fetch_word state 20 (by decide) pc _ (by decide +kernel)

theorem fetch_latch (state : MachineState) (pc : state.pc = cpc 45156) :
    fetch packedWideCommitImage state = some (.base (.BEQ .x20 .x21 64)) :=
  fetch_word state 45156 (by decide) pc _ (by decide +kernel)

theorem fetch_loop_jump (state : MachineState) (pc : state.pc = cpc 45157) :
    fetch packedWideCommitImage state = some (.base (.JAL .x0 1990592)) :=
  fetch_word state 45157 (by decide) pc _ (by decide +kernel)

theorem fetch_exit_jump (state : MachineState) (pc : state.pc = cpc 45177) :
    fetch packedWideCommitImage state = some (.base (.JAL .x0 32768)) :=
  fetch_word state 45177 (by decide) pc _ (by decide +kernel)

end TwoPermutationPrototype.RV64.C3P
