import CommitGolf.Parameters
import Mathlib.Tactic

/-! Byte and instruction accounting for retaining the bottom two internal
levels at 256 bits. Leaves remain 256 bits; higher internal nodes use 240 bits.
This module does not assert execution, security, or a certificate. -/
namespace TwoPermutationPrototype.MixedWidth

def retainedInternalLevels : Nat := 4
def projectedNodeLimit : Nat := 2 ^ 20

def siblingWidth (level : Nat) : Nat := if level ≤ 4 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level ≤ 5 then 16 + 32 * level else 176 + 30 * (level - 5)

def recordBytes : Nat := 506

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level + 1) = siblingOffset level + siblingWidth level := by
  unfold siblingOffset siblingWidth
  split_ifs <;> omega

theorem record_end : siblingOffset 16 = recordBytes := by decide

theorem record_bytes_sum :
    16 + ((List.range 16).map siblingWidth).sum = recordBytes := by decide

theorem record_growth : recordBytes = 498 + 8 := by decide

theorem scored_proof_bytes : recordBytes * 128 + 30 * 128 = 68608 := by decide

theorem scored_opening_cycles : 88311 + 8 * 128 = 89335 := by decide

theorem retained_parent_count : 2 ^ 23 + 2 ^ 22 + 2 ^ 21 + 2 ^ 20 = 15728640 := by decide

theorem sibling_width_even (level : Nat) : siblingWidth level % 2 = 0 := by
  unfold siblingWidth
  split <;> decide

theorem sibling_offset_even (level : Nat) : siblingOffset level % 2 = 0 := by
  unfold siblingOffset
  split <;> omega

end TwoPermutationPrototype.MixedWidth
