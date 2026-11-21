import CommitGolfCandidate.TwoPermutationQuad3Spec
import CommitGolfCandidate.QuadCommitImage

/-! Word addresses and the non-overlap obligations for the quad commit trace.
These facts account for the complete 200-byte writes, including the level-1 group spills and
the level-2 heap spill. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Absolute memory word addresses; the common trapdoor starts at word 536871428. -/
def groupWord (g : Nat) : Nat := 536871428 + 33554935 + 46*g
def leafWord (i : Nat) : Nat := groupWord (i/4) + 9 + 4*(i%4)
def saltWord (i : Nat) : Nat := 536871428 + 226492928 + 2*i
def heapWord (k : Nat) : Nat := 536871428 + 4*k
/-- Quad group `h` (level-2 input) and the slot of level-1 node `g` inside quad group `g/4`. -/
def quad2GroupWord (h : Nat) : Nat := 536871428 + 260048887 + 46*h
def quadSlotWord (g : Nat) : Nat := quad2GroupWord (g/4) + 9 + 4*(g%4)
/-- Level-2 group `m` (level-3 input) and the slot of level-2 node `h` inside level-2 group `h/4`. -/
def quad3GroupWord (m : Nat) : Nat := 536871428 + 4194807 + 46*m
def quad3SlotWord (h : Nat) : Nat := quad3GroupWord (h/4) + 9 + 4*(h%4)
/-- Centered output window, reset after 44 leaves and at the end of each 4096-leaf body. -/
def windowWord (body pos : Nat) : Nat := leafWord (4096*body + 44*(pos/44)) + 221

theorem leaf_byte_address (i : Nat) :
    8 * leafWord i = 4294971424 + quadSlotOffset i := by
  unfold leafWord groupWord quadSlotOffset QUAD_GROUP_BASE
  omega

theorem salt_byte_address (i : Nat) :
    8 * saltWord i = 4294971424 + QUAD_SALT_BASE + 16*i := by
  unfold saltWord QUAD_SALT_BASE
  omega

theorem group_byte_address (g : Nat) :
    8 * groupWord g = 4294971424 + QUAD_GROUP_BASE + 368*g := by
  unfold groupWord QUAD_GROUP_BASE
  omega

theorem heap_byte_address (k : Nat) : 8 * heapWord k = 4294971424 + 32*k := by
  unfold heapWord
  omega

/-- A leaf reply ends by the next group's zero prefix. -/
theorem leaf_write_end (i : Nat) : leafWord i + 25 ≤ groupWord (i/4+1) := by
  unfold leafWord groupWord
  omega

theorem leaf_after_zero_prefix (i : Nat) : groupWord (i/4)+9 ≤ leafWord i := by
  unfold leafWord
  omega

/-- Earlier digest slots survive later leaves, despite the 200-byte replies. -/
theorem leaf_digest_separate (i j : Nat) (ordered : i < j) : leafWord i+4 ≤ leafWord j := by
  unfold leafWord groupWord
  omega

/-- No leaf reply writes any group's 72-byte zero prefix. -/
theorem leaf_zero_prefix_separate (i g : Nat) :
    leafWord i+25 ≤ groupWord g ∨ groupWord g+9 ≤ leafWord i := by
  by_cases earlier : i/4 < g
  · left
    have := leaf_write_end i
    unfold groupWord at *
    omega
  · right
    have := leaf_after_zero_prefix i
    unfold groupWord at *
    omega

theorem leaf_salt_separate (i j : Nat) (inside : i < LENGTH) : leafWord i+25 ≤ saltWord j := by
  have endWrite := leaf_write_end i
  unfold groupWord saltWord at *
  rw [length_value] at inside
  omega

theorem quad_slot_byte_address (g : Nat) :
    8 * quadSlotWord g = 4294971424 + quad2SlotOffset g := by
  unfold quadSlotWord quad2GroupWord quad2SlotOffset QUAD2_GROUP_BASE QUAD_SALT_BASE
  rw [length_value]
  omega

theorem quad2_group_byte_address (h : Nat) :
    8 * quad2GroupWord h = 4294971424 + QUAD2_GROUP_BASE + 368*h := by
  unfold quad2GroupWord QUAD2_GROUP_BASE QUAD_SALT_BASE
  rw [length_value]
  omega

/-- The leaf groups, salts and NonceChain tail all lie below quad group 0. -/
theorem salts_below_quad_groups (i : Nat) (inside : i < LENGTH) : saltWord i + 2 ≤ quad2GroupWord 0 := by
  unfold saltWord quad2GroupWord
  rw [length_value] at inside
  omega

theorem leaf_groups_below_quad_groups (g : Nat) (inside : g < LENGTH/4) : groupWord g + 46 ≤ quad2GroupWord 0 := by
  unfold groupWord quad2GroupWord
  rw [length_value] at inside
  omega

/-- A level-1 reply ends by the next quad group's zero prefix. -/
theorem quad_slot_write_end (g : Nat) : quadSlotWord g + 25 ≤ quad2GroupWord (g/4+1) := by
  unfold quadSlotWord quad2GroupWord
  omega

theorem quad_slot_after_zero_prefix (g : Nat) : quad2GroupWord (g/4)+9 ≤ quadSlotWord g := by
  unfold quadSlotWord
  omega

/-- Earlier level-1 slots survive later level-1 replies. -/
theorem quad_slot_separate (g h : Nat) (ordered : g < h) : quadSlotWord g+4 ≤ quadSlotWord h := by
  unfold quadSlotWord quad2GroupWord
  omega

/-- No level-1 reply writes any quad group's 72-byte zero prefix. -/
theorem quad_slot_zero_prefix_separate (g h : Nat) :
    quadSlotWord g+25 ≤ quad2GroupWord h ∨ quad2GroupWord h+9 ≤ quadSlotWord g := by
  by_cases earlier : g/4 < h
  · left
    have := quad_slot_write_end g
    unfold quad2GroupWord at *
    omega
  · right
    have := quad_slot_after_zero_prefix g
    unfold quad2GroupWord at *
    omega

/-- The last level-1 reply ends 72 bytes before the end of the trapdoor. -/
theorem quad_slot_write_inside (g : Nat) (inside : g < LENGTH/4) :
    8 * (quadSlotWord g + 25) + 72 ≤ 4294971424 + QUAD2_TRAPDOOR_BYTES := by
  unfold quadSlotWord quad2GroupWord QUAD2_TRAPDOOR_BYTES QUAD2_GROUP_BASE QUAD_SALT_BASE
  rw [length_value] at *
  omega

/-- The next quad group starts 272 bytes after the fourth level-1 slot. -/
theorem quad_group_slot_advance (h : Nat) : quadSlotWord (4*h+3)+34 = quadSlotWord (4*(h+1)) := by
  unfold quadSlotWord quad2GroupWord
  omega

theorem quad_slot_advance (g : Nat) (within : g%4 < 3) : quadSlotWord g+4 = quadSlotWord (g+1) := by
  unfold quadSlotWord quad2GroupWord
  omega

/-- The ascending level-2 reply only overlaps higher heap slots. -/
theorem quad2_keeps_earlier_digest (g h : Nat) (earlier : h < g) :
    heapWord (LENGTH/16+h)+4 ≤ heapWord (LENGTH/16+g) := by
  unfold heapWord
  omega

/-- Even the final level-2 reply ends far below the leaf groups. -/
theorem quad2_write_end (g : Nat) (inside : g < LENGTH/16) :
    heapWord (LENGTH/16+g)+25 ≤ groupWord 0 := by
  unfold heapWord groupWord
  rw [length_value] at *
  omega

theorem quad2_spill_exact :
    8 * (heapWord (LENGTH/8-1)+25) = 4294971424 + 2^26 + 168 := by decide

/-- All binary parent inputs are finalized when decreasing from LENGTH/4-1 to 1. -/
theorem binary_children_later (node : Nat) (positive : 0 < node) :
    node < 2*node ∧ node < 2*node+1 := by omega

theorem binary_write_before_quads (node : Nat) (branch : node < LENGTH/16) :
    heapWord node+4 ≤ heapWord (LENGTH/16) := by
  unfold heapWord
  omega

theorem layout_trapdoor_size (opening checker : Image) :
    (submission opening checker).sizes.trapdoor = QUAD2_TRAPDOOR_BYTES := rfl

theorem layout_buffer_positions (opening checker : Image) :
    (submission opening checker).layout.indices = 4294971424 + QUAD2_TRAPDOOR_BYTES ∧
    (submission opening checker).layout.values = 4294971424 + QUAD2_TRAPDOOR_BYTES + 2^27 + 64 ∧
    (submission opening checker).layout.proof = 4294971424 + QUAD2_TRAPDOOR_BYTES + 2^27 + 64 + 2^32 := by
  change 6761238560 = _ ∧ 6895456352 = _ ∧ 11190423648 = _
  decide

theorem layout_proof_capacity (opening checker : Image) :
    (submission opening checker).sizes.proof = QUAD3_PROOF_CAPACITY := rfl

theorem quad3_slot_byte_address (h : Nat) :
    8 * quad3SlotWord h = 4294971424 + quad3SlotOffset h := by
  unfold quad3SlotWord quad3GroupWord quad3SlotOffset QUAD3_GROUP_BASE
  omega

theorem quad3_group_byte_address (m : Nat) :
    8 * quad3GroupWord m = 4294971424 + QUAD3_GROUP_BASE + 368*m := by
  unfold quad3GroupWord QUAD3_GROUP_BASE
  omega

/-- A level-2 reply ends by the next level-2 group's zero prefix. -/
theorem quad3_slot_write_end (h : Nat) : quad3SlotWord h + 25 ≤ quad3GroupWord (h/4+1) := by
  unfold quad3SlotWord quad3GroupWord
  omega

theorem quad3_slot_after_zero_prefix (h : Nat) : quad3GroupWord (h/4)+9 ≤ quad3SlotWord h := by
  unfold quad3SlotWord
  omega

theorem quad3_slot_separate (g h : Nat) (ordered : g < h) : quad3SlotWord g+4 ≤ quad3SlotWord h := by
  unfold quad3SlotWord quad3GroupWord
  omega

theorem quad3_slot_zero_prefix_separate (h m : Nat) :
    quad3SlotWord h+25 ≤ quad3GroupWord m ∨ quad3GroupWord m+9 ≤ quad3SlotWord h := by
  by_cases earlier : h/4 < m
  · left
    have := quad3_slot_write_end h
    unfold quad3GroupWord at *
    omega
  · right
    have := quad3_slot_after_zero_prefix h
    unfold quad3GroupWord at *
    omega

/-- Every level-2 reply ends below the leaf groups. -/
theorem quad3_slot_write_below (h : Nat) (inside : h < LENGTH/16) : quad3SlotWord h + 25 ≤ groupWord 0 := by
  unfold quad3SlotWord quad3GroupWord groupWord
  rw [length_value] at inside
  omega

/-- Even the final level-3 reply ends below the level-2 groups. -/
theorem quad3_heap_write_end (m : Nat) (inside : m < LENGTH/64) :
    heapWord (LENGTH/64+m)+25 ≤ quad3GroupWord 0 := by
  unfold heapWord quad3GroupWord
  rw [length_value] at *
  omega

theorem quad3_spill_exact :
    8 * (heapWord (LENGTH/32-1)+25) = 4294971424 + 2^24 + 168 := by decide

/-- The next group starts 272 bytes after the fourth leaf slot. -/
theorem group_slot_advance (g : Nat) : leafWord (4*g+3)+34 = leafWord (4*(g+1)) := by
  unfold leafWord groupWord
  omega

/-- The destination range fits a signed twelve-bit immediate. -/
theorem slot_immediate_range (u : Nat) :
    -2048 ≤ (-1768 + 368 * Int.ofNat ((u%44)/4) + 32 * Int.ofNat (u%4)) ∧
    (-1768 + 368 * Int.ofNat ((u%44)/4) + 32 * Int.ofNat (u%4)) ≤ 2047 := by
  change -2048 ≤ (-1768 + 368 * (((u%44)/4 : Nat) : Int) + 32 * ((u%4 : Nat) : Int)) ∧
    (-1768 + 368 * (((u%44)/4 : Nat) : Int) + 32 * ((u%4 : Nat) : Int)) ≤ 2047
  have h44 := Nat.mod_lt u (by decide : 0 < 44)
  have h4 := Nat.mod_lt u (by decide : 0 < 4)
  omega

/-- Number of output-window rebases in one unrolled leaf body. -/
theorem leaf_rebase_count :
    ((List.range 4096).filter (fun u => u%44=43 ∨ u=4095)).length = 94 := by decide +kernel

theorem salt_rebase_count :
    ((List.range 4096).filter (fun u => u%128=127)).length = 32 := by decide +kernel

end TwoPermutationPrototype.Quad.Commit
