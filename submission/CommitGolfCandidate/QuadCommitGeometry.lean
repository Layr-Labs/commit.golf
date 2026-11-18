import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.QuadCommitImage

/-! Word addresses and the non-overlap obligations for the quad commit trace.
These facts account for the complete 200-byte writes, including the quad heap spill. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Absolute memory word addresses; the common trapdoor starts at word 536871428. -/
def groupWord (g : Nat) : Nat := 536871428 + 33554935 + 46*g
def leafWord (i : Nat) : Nat := groupWord (i/4) + 9 + 4*(i%4)
def saltWord (i : Nat) : Nat := 536871428 + 226492928 + 2*i
def heapWord (k : Nat) : Nat := 536871428 + 4*k
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

/-- The ascending quad reply only overlaps higher heap slots. -/
theorem quad_keeps_earlier_digest (g h : Nat) (earlier : h < g) :
    heapWord (LENGTH/4+h)+4 ≤ heapWord (LENGTH/4+g) := by
  unfold heapWord
  omega

/-- Even the final quad reply ends before the leaf groups, inside the 512-byte padding. -/
theorem quad_write_end (g : Nat) (inside : g < LENGTH/4) :
    heapWord (LENGTH/4+g)+25 ≤ groupWord 0 := by
  unfold heapWord groupWord
  rw [length_value] at *
  omega

theorem quad_spill_exact :
    8 * (heapWord (LENGTH/2-1)+25) = 4294971424 + 2^28 + 168 := by decide

/-- All binary parent inputs are finalized when decreasing from LENGTH/4-1 to 1. -/
theorem binary_children_later (node : Nat) (positive : 0 < node) :
    node < 2*node ∧ node < 2*node+1 := by omega

theorem binary_write_before_quads (node : Nat) (branch : node < LENGTH/4) :
    heapWord node+4 ≤ heapWord (LENGTH/4) := by
  unfold heapWord
  omega

theorem layout_trapdoor_size (opening checker : Image) :
    (submission opening checker).sizes.trapdoor = QUAD_TRAPDOOR_BYTES := rfl

theorem layout_buffer_positions (opening checker : Image) :
    (submission opening checker).layout.indices = 4294971424 + QUAD_TRAPDOOR_BYTES ∧
    (submission opening checker).layout.values = 4294971424 + QUAD_TRAPDOOR_BYTES + 2^27 + 64 ∧
    (submission opening checker).layout.proof = 4294971424 + QUAD_TRAPDOOR_BYTES + 2^27 + 64 + 2^32 := by
  change 6375350304 = _ ∧ 6509568096 = _ ∧ 10804535392 = _
  decide

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
