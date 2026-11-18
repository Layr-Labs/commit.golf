import CommitGolf.Parameters
import Mathlib.Tactic

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf

def quartetCount : Nat := LENGTH / 4
def quartetOffset (group : Nat) : Nat := 368 * group

def quartetLeafOffset (index : Nat) : Nat :=
  quartetOffset (index / 4) + 72 + 32 * (index % 4)

def upperLeafOffset (group : Nat) : Nat := 32 * (quartetCount + group)
def quartetBaseOffset : Nat := 68 * LENGTH
def saltBaseOffset : Nat := quartetBaseOffset + 368 * quartetCount

theorem quartet_count : quartetCount = 4194304 := rfl

theorem base_offsets :
    quartetBaseOffset = 1140850688 ∧ saltBaseOffset = 2684354560 := by
  decide

theorem quartet_leaf_offset_exact (group pos : Nat) (valid : pos < 4) :
    quartetLeafOffset (4 * group + pos) = quartetOffset group + 72 + 32 * pos := by
  unfold quartetLeafOffset quartetOffset
  omega

theorem quartet_input_partition (index : Nat) :
    quartetOffset (index / 4) ≤ quartetLeafOffset index ∧
    quartetLeafOffset index + 32 ≤ quartetOffset (index / 4) + 200 := by
  simp only [quartetLeafOffset]
  omega

theorem quartet_leaf_write_frame (index : Nat) :
    quartetOffset (index / 4) + 72 ≤ quartetLeafOffset index ∧
    quartetLeafOffset index + 200 ≤ quartetOffset (index / 4 + 1) := by
  unfold quartetLeafOffset quartetOffset
  omega

theorem later_leaf_keeps_prior_digest (early late : Nat) (lt : early < late) :
    quartetLeafOffset early + 32 ≤ quartetLeafOffset late := by
  unfold quartetLeafOffset quartetOffset
  omega

theorem quartet_input_stays_before_salts (group : Nat) (valid : group < quartetCount) :
    quartetBaseOffset + quartetOffset group + 200 ≤ saltBaseOffset := by
  unfold quartetOffset saltBaseOffset
  omega

theorem upper_output_spill_stays_before_quartets (group : Nat) (valid : group < quartetCount) :
    upperLeafOffset group + 200 ≤ quartetBaseOffset := by
  rw [quartet_count] at valid
  unfold upperLeafOffset
  rw [quartet_count]
  have exactBase : quartetBaseOffset = 1140850688 := base_offsets.1
  omega

def centeredLeafOffset (index : Nat) : Int :=
  512 * (((index / 4) % 8 : Nat) : Int) - 2048 + 72 + 32 * ((index % 4 : Nat) : Int)

theorem centered_leaf_offset_fits (index : Nat) :
    -2048 ≤ centeredLeafOffset index ∧ centeredLeafOffset index < 2048 := by
  unfold centeredLeafOffset
  omega

def commitCycles : Nat :=
  22 + 2*LENGTH + 25*LENGTH + LENGTH/32 + LENGTH/256 +
  (2*(LENGTH/4096)-1) + 3 + 10*quartetCount +
  (2*(quartetCount/512)-1) + 6 + 11*(quartetCount-1) +
  (2*((quartetCount-1)/32767)-1) + 11

theorem commit_cycles_exact : commitCycles = 541679900 := by
  decide

theorem commit_calls_exact :
    2 * LENGTH + quartetCount + (quartetCount - 1) = 41943039 := by decide

end TwoPermutationPrototype.QuartetCommit
