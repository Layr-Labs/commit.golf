import CommitGolfCandidate.QOpeningResources
import CommitGolfCandidate.QOpeningGeometry
import CommitGolfCandidate.TwoPermutationQuad2Spec

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf TwoPermutationPrototype.Sampling

/-- Quad2 lower path: level 0 is the quad2 node `(LENGTH + index) / 16`, level `l` is
`(LENGTH + index) / 2^(l+4)`. -/
def lowerNode (index : Index) (level : Nat) : Nat := QOpening.lowerNode index (level+4)

theorem lower_node_next (index : Index) (level : Nat) :
    lowerNode index (level+1) = lowerNode index level / 2 := QOpening.lower_node_next index (level+4)

theorem lower_node_bound (index : Index) (level : Nat) : lowerNode index level < 2 * LENGTH :=
  QOpening.lower_node_bound index (level+4)

theorem lower_swap_bound (index : Index) (level : Nat) : lowerNode index level ^^^ 1 < 2 * LENGTH :=
  QOpening.lower_swap_bound index (level+4)

theorem lower_cap_range (index : Index) : 256 ≤ lowerNode index 12 ∧ lowerNode index 12 < 512 :=
  QOpening.lower_cap_range index

def recordBytes : Nat := 570
def capacity : Nat := recordBytes * LENGTH + 30*256

theorem capacity_value : capacity = QUAD2_PROOF_CAPACITY := rfl

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


def siblingWidth (level : Nat) : Nat := if level = 0 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level = 0 then 208 else 240+30*(level-1)

def recordBase (ordinal : Nat) : Nat := QOpening.proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

/-- Record offset of the `j`-th neighbour leaf digest (rotation order, `j < 3`). -/
def leafOffset (j : Nat) : Nat := 16+32*j

def leafDestination (ordinal j : Nat) : Nat := recordBase ordinal+leafOffset j

theorem even_leaf_destination (ordinal j : Nat) : leafDestination ordinal j % 2 = 0 := by
  have base : QOpening.proofBase % 2 = 0 := by decide
  unfold leafDestination recordBase recordBytes leafOffset
  omega

/-- Record offset of the `j`-th neighbour quad node (rotation order, `j < 3`). -/
def quadOffset (j : Nat) : Nat := 112+32*j

def quadDestination (ordinal j : Nat) : Nat := recordBase ordinal+quadOffset j

theorem even_quad_destination (ordinal j : Nat) : quadDestination ordinal j % 2 = 0 := by
  have base : QOpening.proofBase % 2 = 0 := by decide
  unfold quadDestination recordBase recordBytes quadOffset
  omega

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  cases level <;> simp [siblingOffset, siblingWidth, Nat.mul_succ] <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 12 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : QOpening.proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> omega

/-! ### Record cycles

A record's copy sites cost `cost32` (32-byte fields) or `cost30` (30-byte siblings) cycles, by the
alignment of their destination; everything else in a record is 138 cycles (692 with halfword copies). -/

def cost32 (target : Nat) : Nat := if target % 8 = 0 then 12 else if target % 8 = 4 then 22 else 30
def cost30 (target : Nat) : Nat := if target % 8 = 0 then 14 else if target % 8 = 4 then 22 else 28

theorem cost32_le (target : Nat) : cost32 target ≤ 32 := by unfold cost32; split_ifs <;> omega
theorem cost30_le (target : Nat) : cost30 target ≤ 30 := by unfold cost30; split_ifs <;> omega

def recordCycles (ordinal : Nat) : Nat :=
  138+cost32 (leafDestination ordinal 0)+cost32 (leafDestination ordinal 1)+cost32 (leafDestination ordinal 2)+
    cost32 (quadDestination ordinal 0)+cost32 (quadDestination ordinal 1)+cost32 (quadDestination ordinal 2)+
    cost32 (siblingDestination ordinal 0)+cost30 (siblingDestination ordinal 1)+cost30 (siblingDestination ordinal 2)+
    cost30 (siblingDestination ordinal 3)+cost30 (siblingDestination ordinal 4)+cost30 (siblingDestination ordinal 5)+
    cost30 (siblingDestination ordinal 6)+cost30 (siblingDestination ordinal 7)+cost30 (siblingDestination ordinal 8)+
    cost30 (siblingDestination ordinal 9)+cost30 (siblingDestination ordinal 10)+cost30 (siblingDestination ordinal 11)

def recordsCycles : Nat → Nat
  | 0 => 0
  | n+1 => recordsCycles n+recordCycles n

theorem record_cycles_le (ordinal : Nat) : recordCycles ordinal ≤ 692 := by
  unfold recordCycles
  have := cost32_le (leafDestination ordinal 0); have := cost32_le (leafDestination ordinal 1)
  have := cost32_le (leafDestination ordinal 2); have := cost32_le (quadDestination ordinal 0)
  have := cost32_le (quadDestination ordinal 1); have := cost32_le (quadDestination ordinal 2)
  have := cost32_le (siblingDestination ordinal 0); have := cost30_le (siblingDestination ordinal 1)
  have := cost30_le (siblingDestination ordinal 2); have := cost30_le (siblingDestination ordinal 3)
  have := cost30_le (siblingDestination ordinal 4); have := cost30_le (siblingDestination ordinal 5)
  have := cost30_le (siblingDestination ordinal 6); have := cost30_le (siblingDestination ordinal 7)
  have := cost30_le (siblingDestination ordinal 8); have := cost30_le (siblingDestination ordinal 9)
  have := cost30_le (siblingDestination ordinal 10); have := cost30_le (siblingDestination ordinal 11)
  omega

theorem record_cycles_pos (ordinal : Nat) : 138 ≤ recordCycles ordinal := by
  unfold recordCycles; omega

theorem records_cycles_le (n : Nat) : recordsCycles n ≤ 692*n := by
  induction n with
  | zero => rfl
  | succ n ih => have := record_cycles_le n; simp only [recordsCycles]; omega

theorem records_cycles_pos (n : Nat) (positive : 0 < n) : 1 ≤ recordsCycles n := by
  cases n with
  | zero => omega
  | succ n => have := record_cycles_pos n; simp only [recordsCycles]; omega

set_option maxRecDepth 100000 in
theorem records_cycles_batch : recordsCycles 128 = 71104 := by decide

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    17 + (recordsCycles positions.card-1) + 2551 +
      (capSubtreeCycles (QOpening.groupsBefore positions positions.card) 1 8 + 3) + 4

theorem proof_fits_every_cardinality (positions : Positions) :
    proofLength positions ≤ capacity := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have nodes := QOpening.opening_nodes_bound positions
  unfold proofLength capacity recordBytes
  omega

theorem scheduled_fuel_fits (positions : Positions) : scheduledCycles positions ≤ 17179934720 := by
  have rc := records_cycles_le positions.card
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
    scheduledCycles positions ≤ 83899 ∧ proofLength positions ≤ 76800 := by
  have size : positions.card = 128 := count
  have rc : recordsCycles positions.card = 71104 := by rw [size]; exact records_cycles_batch
  have cap := QOpening.opening_cap_cycles_bound (QOpening.groupsBefore positions positions.card)
  have bytes := QOpening.opening_nodes_bound positions
  have positive : positions.card ≠ 0 := by omega
  rw [scheduledCycles, ite_eq_right positive, cap_cycle_delta]
  unfold proofLength recordBytes
  simp only [QOpening.openingNodes, ite_eq_right positive] at bytes ⊢
  omega

theorem scheduled_scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧ scheduledCycles positions = 83899 ∧
      proofLength positions = 76800 := by
  obtain ⟨positions, count, cycles, bytes⟩ := QOpening.opening_scored_attainment
  have size : positions.card = 128 := count
  have rc : recordsCycles positions.card = 71104 := by rw [size]; exact records_cycles_batch
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
