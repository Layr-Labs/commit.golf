import CommitGolfCandidate.TwoPermutationOpeningResources

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf TwoPermutationPrototype.Sampling

def recordBytes : Nat := 504
def capacity : Nat := recordBytes * LENGTH + 30*256

def proofLength (positions : Positions) : Nat :=
  recordBytes*positions.card + 30*(Opening.openingNodes positions).length

/-- Packed frontier emission replaces a 32-byte doubleword copy with 15 pairs of halfword instructions. -/
def capSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 37
  | height+1 =>
    if capIsMarked groups node (height+1) then
      15 + capSubtreeCycles groups (2*node) height + capSubtreeCycles groups (2*node+1) height
    else 37

private def capWorst : Nat → Nat
  | 0 => 57
  | remaining + 1 => 15 + 2 * capWorst remaining

private theorem cap_worst_positive (n : Nat) : 37 ≤ capWorst n := by
  induction n with
  | zero => decide
  | succ n ih => rw [capWorst]; omega

private theorem cap_subtree_sharp_bound (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node (height+1) ≤ capWorst height := by
  induction height generalizing node with
  | zero =>
    rw [capSubtreeCycles, cap_marked_children]
    cases left : capIsMarked groups (2*node) 0 <;>
      cases right : capIsMarked groups (2*node+1) 0 <;>
      simp [capSubtreeCycles, capWorst, left, right]
  | succ height ih =>
    have positive := cap_worst_positive height
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [capSubtreeCycles, capWorst]
    split <;> omega

/-- A marked height-one subtree must contain at least one occupied leaf. Its
worst case is 57 cycles, which yields the tight bound at the production cap. -/
theorem opening_cap_cycles_bound (groups : List Nat) :
    capSubtreeCycles groups 1 8 ≤ 9201 :=
  cap_subtree_sharp_bound groups 1 7

def scheduledCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    13 + (596*positions.card-1) + 769 +
      (capSubtreeCycles (Opening.groupsBefore positions positions.card) 1 8 + 5) + 4

def siblingWidth (level : Nat) : Nat := if level ≤ 3 then 32 else 30

def siblingOffset (level : Nat) : Nat :=
  if level ≤ 4 then 16+32*level else 144+30*(level-4)

def recordBase (ordinal : Nat) : Nat := Opening.proofBase+recordBytes*ordinal

def siblingDestination (ordinal level : Nat) : Nat := recordBase ordinal+siblingOffset level

theorem sibling_offset_next (level : Nat) :
    siblingOffset (level+1) = siblingOffset level+siblingWidth level := by
  unfold siblingOffset siblingWidth
  split_ifs <;> omega

theorem record_end (ordinal : Nat) :
    siblingDestination ordinal 16 = recordBase (ordinal+1) := by
  simp [siblingDestination, recordBase, recordBytes, siblingOffset]
  omega

theorem even_sibling_destination (ordinal level : Nat) :
    siblingDestination ordinal level % 2 = 0 := by
  have base : Opening.proofBase % 2 = 0 := by decide
  unfold siblingDestination recordBase recordBytes siblingOffset
  split <;> omega

theorem proof_fits_every_cardinality (positions : Positions) :
    proofLength positions ≤ capacity := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have nodes := Opening.opening_nodes_bound positions
  unfold proofLength capacity recordBytes
  omega

theorem scheduled_fuel_fits (positions : Positions) : scheduledCycles positions ≤ 17179934720 := by
  have cardinal : positions.card ≤ 16777216 := by
    have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  unfold scheduledCycles
  split
  · decide
  · have counts := opening_cap_cycles_bound (Opening.groupsBefore positions positions.card)
    have nodes := Opening.opening_nodes_bound positions
    simp only [Opening.openingNodes, ite_eq_right (by assumption)] at nodes
    omega

theorem scheduled_scored_limits (positions : Positions) (count : positions.card = BATCH) :
    scheduledCycles positions ≤ 86279 ∧ proofLength positions ≤ 68352 := by
  have size : positions.card = 128 := count
  have cap := opening_cap_cycles_bound (Opening.groupsBefore positions positions.card)
  have bytes := Opening.opening_nodes_bound positions
  have positive : positions.card ≠ 0 := by omega
  rw [scheduledCycles, ite_eq_right positive]
  unfold proofLength recordBytes
  simp only [Opening.openingNodes, ite_eq_right positive] at bytes ⊢
  omega

private def scatteredIndex : Fin 128 ↪ Index where
  toFun i := ⟨131072*i.val, by
    have bounded := i.isLt
    norm_num [LENGTH, LOG_LENGTH]
    omega⟩
  inj' := by
    intro a b same
    have values := congrArg Fin.val same
    apply Fin.ext
    change 131072*a.val = 131072*b.val at values
    omega

private def scattered128 : Positions := (Finset.univ : Finset (Fin 128)).map scatteredIndex

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- One request per even cap group attains both sharp scored opening bounds. -/
theorem scheduled_scored_attainment :
    ∃ positions : Positions, positions.card = BATCH ∧
      scheduledCycles positions = 86279 ∧ proofLength positions = 68352 := by
  have count : scattered128.card = 128 := by decide
  let groups := ((List.finRange 128).map scatteredIndex).map capGroup
  have order : scattered128.sort (· ≤ ·) = (List.finRange 128).map scatteredIndex := by
    have transport := Finset.map_sort (r := fun a b : Fin 128 => a ≤ b)
      (r' := fun a b : Index => a ≤ b) (f := scatteredIndex) (s := Finset.univ)
      (by
        intro a _ b _
        change a.val ≤ b.val ↔ 131072*a.val ≤ 131072*b.val
        omega)
    simpa only [scattered128, Fin.sort_univ] using transport.symm
  have exactGroups : Opening.groupsBefore scattered128 128 = groups := by
    unfold Opening.groupsBefore groups
    rw [order, List.take_of_length_le (by simp)]
  have cap : capSubtreeCycles groups 1 8 = 9201 := by decide
  have frontier : (capFrontierNodes groups 1 8).length = 128 := by decide
  refine ⟨scattered128, count, ?_, ?_⟩
  · simp [scheduledCycles, count, exactGroups, cap]
  · simp [proofLength, recordBytes, Opening.openingNodes, count, exactGroups, frontier]

end TwoPermutationPrototype.PackedOpening
