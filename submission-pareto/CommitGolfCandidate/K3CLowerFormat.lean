import CommitGolfCandidate.TwoPermutationPackedCheckCursor
import Mathlib.Tactic.SplitIfs

/-! # Byte layout of a record's upper siblings (final stack, T238 format of STATUS-t238p)

A record is `recordBytes = 534` bytes: salt (16), the three quartet siblings (96), then the fourteen upper siblings of
loop levels `L = 0..13`. Loop level `L` reads the sibling of tree level `22 - L`: 32 bytes for `L ≤ 1` (the quartet
node and, with L21, the untruncated level-21 node) at `record + 112 + 32 L`, a 30-byte slot for `L = 2..12` at
`record + 176 + 30 (L - 2)` and a 28-byte slot for `L = 13` at `record + 506` (levels `L ≥ 6` hold the packed
238-bit block, decoded by `packedSibling`). The cursor at `L = 14` is the next record. The loop's 30-byte copy at
`L = 13` reads two bytes past the record, so the step's room is `checkProofByte ordinal + 536 ≤ MEMORY_BYTES`. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv

/-- Bytes per opened position in the proof. -/
def recordBytes : Nat := 534

/-- Byte cursor before the upper sibling of loop level `level`, or after the record at level fourteen. -/
def lowerProofByte (ordinal level : Nat) : Nat :=
  if level ≤ 1 then checkProofByte ordinal+112+32*level
  else if level ≤ 13 then checkProofByte ordinal+176+30*(level-2) else checkProofByte ordinal+534

def lowerSiblingWidth (level : Nat) : Nat := if level ≤ 1 then 32 else if level ≤ 12 then 30 else 28

theorem lower_proof_byte_next (ordinal level : Nat) (inside : level < 14) :
    lowerProofByte ordinal (level+1) = lowerProofByte ordinal level+lowerSiblingWidth level := by
  unfold lowerProofByte lowerSiblingWidth
  by_cases zero : level = 0
  · subst level; simp
  · by_cases one : level = 1
    · subst level; simp
    · by_cases last : level = 13
      · subst level; simp
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
          if_pos (by omega)]
        omega

theorem lower_proof_byte_end (ordinal : Nat) :
    lowerProofByte ordinal 14 = checkProofByte (ordinal+1) := by
  unfold lowerProofByte checkProofByte
  rw [if_neg (by decide), if_neg (by decide)]
  omega

theorem lower_proof_byte_bounds (ordinal level : Nat) (inside : level < 14)
    (room : checkProofByte ordinal+536 ≤ MEMORY_BYTES) :
    32768 ≤ lowerProofByte ordinal level ∧ lowerProofByte ordinal level % 2 = 0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level ≤ MEMORY_BYTES := by
  unfold lowerProofByte lowerSiblingWidth
  unfold checkProofByte at room ⊢
  change 13824430176+534*ordinal+536 ≤ 2^36 at room
  change _ ∧ _ ∧ _ ≤ 2^36
  split_ifs <;> omega

end TwoPermutationPrototype.Packed.Checker
