import CommitGolfCandidate.QOpeningResources
import CommitGolfCandidate.QOpeningGeometry

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf TwoPermutationPrototype.Sampling

/-- Quad lower path: level 0 is the quad node `(LENGTH + index) / 4`, level `l` is `(LENGTH + index) / 2^(l+2)`. -/
def lowerNode (index : Index) (level : Nat) : Nat := QOpening.lowerNode index (level+2)

theorem lower_node_next (index : Index) (level : Nat) :
    lowerNode index (level+1) = lowerNode index level / 2 := QOpening.lower_node_next index (level+2)

theorem lower_node_bound (index : Index) (level : Nat) : lowerNode index level < 2 * LENGTH :=
  QOpening.lower_node_bound index (level+2)

theorem lower_swap_bound (index : Index) (level : Nat) : lowerNode index level ^^^ 1 < 2 * LENGTH :=
  QOpening.lower_swap_bound index (level+2)

theorem lower_cap_range (index : Index) : 256 ≤ lowerNode index 14 ∧ lowerNode index 14 < 512 :=
  QOpening.lower_cap_range index

def recordBytes : Nat := 534
def capacity : Nat := recordBytes * LENGTH + 30*256

def proofLength (positions : Positions) : Nat :=
  recordBytes*positions.card + 30*(QOpening.openingNodes positions).length

/-- Packed frontier emission replaces a 32-byte doubleword copy with 15 pairs of halfword instructions. -/
def capSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 37
  | height+1 =>
    if capIsMarked groups node (height+1) then
      19 + capSubtreeCycles groups (2*node) height + capSubtreeCycles groups (2*node+1) height
    else 37

theorem cap_cycle_delta (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node height =
      QOpening.capSubtreeCycles groups node height + 22*(capFrontierNodes groups node height).length := by
  induction height generalizing node with
  | zero =>
    cases marked : capIsMarked groups node 0 <;> simp [capSubtreeCycles, QOpening.capSubtreeCycles, capFrontierNodes, marked]
  | succ height ih =>
    cases marked : capIsMarked groups node (height+1)
    · simp [capSubtreeCycles, QOpening.capSubtreeCycles, capFrontierNodes, marked]
    · simp only [capSubtreeCycles, QOpening.capSubtreeCycles, capFrontierNodes, marked, ite_true,
        List.length_append, ih (2*node), ih (2*node+1)]
      omega

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    15 + (641*positions.card-1) + 2551 +
      (capSubtreeCycles (QOpening.groupsBefore positions positions.card) 1 8 + 3) + 4

def siblingWidth (level : Nat) : Nat := if level = 0 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level = 0 then 112 else 144+30*(level-1)

def recordBase (ordinal : Nat) : Nat := QOpening.proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

/-- Record offset of the `j`-th neighbour leaf digest (rotation order, `j < 3`). -/
def leafOffset (j : Nat) : Nat := 16+32*j

def leafDestination (ordinal j : Nat) : Nat := recordBase ordinal+leafOffset j

theorem even_leaf_destination (ordinal j : Nat) : leafDestination ordinal j % 2 = 0 := by
  have base : QOpening.proofBase % 2 = 0 := by decide
  unfold leafDestination recordBase recordBytes leafOffset
  omega

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  cases level <;> simp [siblingOffset, siblingWidth, Nat.mul_succ] <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 14 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : QOpening.proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> omega

theorem proof_fits_every_cardinality (positions : Positions) :
    proofLength positions ≤ capacity := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have nodes := QOpening.opening_nodes_bound positions
  unfold proofLength capacity recordBytes
  omega

theorem scheduled_fuel_fits (positions : Positions) : scheduledCycles positions ≤ 17179934720 := by
  have cardinal : positions.card ≤ 16777216 := by
    have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  unfold scheduledCycles
  split
  · decide
  · rw [cap_cycle_delta]
    have counts := QOpening.opening_cap_cycles_bound (QOpening.groupsBefore positions positions.card)
    have nodes := QOpening.opening_nodes_bound positions
    simp only [QOpening.openingNodes, ite_eq_right (by assumption)] at nodes
    omega

theorem scheduled_scored_limits (positions : Positions) (count : positions.card = BATCH) :
    scheduledCycles positions ≤ 94841 ∧ proofLength positions ≤ 72192 := by
  have size : positions.card = 128 := count
  have cap := QOpening.opening_cap_cycles_bound (QOpening.groupsBefore positions positions.card)
  have bytes := QOpening.opening_nodes_bound positions
  have positive : positions.card ≠ 0 := by omega
  rw [scheduledCycles, ite_eq_right positive, cap_cycle_delta]
  unfold proofLength recordBytes
  simp only [QOpening.openingNodes, ite_eq_right positive] at bytes ⊢
  omega

theorem scheduled_scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧ scheduledCycles positions = 94841 ∧
      proofLength positions = 72192 := by
  obtain ⟨positions, count, cycles, bytes⟩ := QOpening.opening_scored_attainment
  have size : positions.card = 128 := count
  have positive : positions.card ≠ 0 := by omega
  unfold QOpening.openingMachineCycles at cycles
  rw [ite_eq_right positive] at cycles
  have exactCount : (QOpening.openingNodes positions).length = 128 := by
    unfold QOpening.openingLength at bytes
    omega
  refine ⟨positions, count, ?_, ?_⟩
  · rw [scheduledCycles, ite_eq_right positive, cap_cycle_delta]
    simp only [QOpening.openingNodes, ite_eq_right positive] at exactCount
    omega
  · unfold proofLength recordBytes
    omega

end TwoPermutationPrototype.QuadOpening
