import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv

def recordBytes : Nat := 534
def capacity : Nat := recordBytes * LENGTH + 30*256
def siblingWidth (level : Nat) : Nat := if level = 0 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level = 0 then 112 else 144+30*(level-1)

def recordBase (ordinal : Nat) : Nat := proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  cases level <;> simp [siblingOffset, siblingWidth, Nat.mul_succ] <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 14 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> omega

end TwoPermutationPrototype.GroupedOpening
