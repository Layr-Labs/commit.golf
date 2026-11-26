import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv

/-! Record layout (534 bytes): salt 16 | three mates 96 | writer levels `l = 0, 1` (group sibling and the
level-21 sibling) 32 bytes each | `l = 2..12` 30 bytes each | `l = 13` 28 bytes. The slots of `l = 6..12`
also carry two bits of the `l = 13` node in bits 14, 15 of their halfword at byte 28 (the T238 fold). -/

def recordBytes : Nat := 534
def capacity : Nat := recordBytes * LENGTH + 30*256

/-- Bytes of the heap node copied by writer level `level`. -/
def siblingWidth (level : Nat) : Nat := if level < 2 then 32 else if level < 13 then 30 else 28

def siblingOffset (level : Nat) : Nat :=
  if level < 2 then 112+32*level else if level < 14 then 176+30*(level-2) else 534

def recordBase (ordinal : Nat) : Nat := proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

/-- The packed levels whose halfword at byte 28 is folded: slot `k = level-6`. -/
def folded (level : Nat) : Prop := 6 ≤ level ∧ level < 13

instance (level : Nat) : Decidable (folded level) := by unfold folded; infer_instance

/-- Bytes of a level that keep the plain heap copy: all but the folded halfword (bytes 28, 29). -/
def plainWidth (level : Nat) : Nat := if folded level then 28 else siblingWidth level

theorem sibling_width_le (level : Nat) : siblingWidth level ≤ 32 := by
  unfold siblingWidth; split <;> (try split) <;> omega

theorem plain_width_le (level : Nat) : plainWidth level ≤ siblingWidth level := by
  unfold plainWidth folded siblingWidth; split <;> (try split) <;> (try split) <;> omega

theorem sibling_offset_next (level : Nat) (inside : level < 14) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  unfold siblingOffset siblingWidth
  by_cases a : level < 1
  · have : level = 0 := by omega
    subst level; decide
  · by_cases b : level < 2
    · have : level = 1 := by omega
      subst level; decide
    · by_cases c : level < 13
      · rw [if_neg (by omega), if_pos (by omega), if_neg b, if_pos (by omega), if_neg b, if_pos c]
        omega
      · have : level = 13 := by omega
        subst level; decide

theorem sibling_offset_mono : Monotone siblingOffset := by
  intro a b le
  unfold siblingOffset
  split_ifs <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 14 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> (try split) <;> omega

theorem sibling_offset_le (level : Nat) (inside : level ≤ 14) : siblingOffset level ≤ 534 := by
  unfold siblingOffset; split <;> (try split) <;> omega

theorem sibling_offset_start (level : Nat) : 112 ≤ siblingOffset level := by
  unfold siblingOffset; split <;> (try split) <;> omega

theorem sibling_inside_record (level : Nat) (inside : level < 14) :
    siblingOffset level+siblingWidth level ≤ recordBytes := by
  rw [← sibling_offset_next level inside]
  exact sibling_offset_le (level+1) (by omega)

/-- The fold slot `k < 7` is writer level `6+k`; its halfword at byte 28 lies 182-30k bytes below
level 13's slot. -/
theorem fold_slot_offset (ordinal k : Nat) (inside : k < 7) :
    siblingDestination ordinal (6+k)+28+(182-30*k) = siblingDestination ordinal 13 := by
  unfold siblingDestination siblingOffset
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
  omega

end TwoPermutationPrototype.GroupedOpening
