import CommitGolfCandidate.TwoPermutationPackedOpeningModel
import Mathlib.Data.Nat.Bitwise

/-! # The leader's proof from a trapdoor that is right only where the records read it

The paired opener's trapdoor′ holds the honest internal nodes, and for each opened leaf its salt and its
mate's digest; the other leaf slots hold reply bytes. The proof reads nothing else. -/
namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open Opening (groupsBefore lower_swap_bound lowerNode trapdoorHeap trapdoorSalt openingNodes
  cap_frontier_nodes_small cap_span_root cap_span_node cap_span_children)
set_option autoImplicit false

theorem xor_one_even {n : Nat} (h : n % 2 = 0) : n ^^^ 1 = n + 1 := Nat.xor_one_of_even (Nat.even_iff.mpr h)

theorem xor_one_odd {n : Nat} (h : n % 2 = 1) : n ^^^ 1 = n - 1 := Nat.xor_one_of_odd (Nat.odd_iff.mpr h)

theorem leaf_mate_node (i : Nat) (hi : i < LENGTH) : (LENGTH + i) ^^^ 1 = LENGTH + (i ^^^ 1) := by
  have hL : LENGTH = 16777216 := rfl
  by_cases e : i % 2 = 0
  · rw [xor_one_even (by omega), xor_one_even e]; omega
  · rw [xor_one_odd (by omega), xor_one_odd (by omega)]; omega

private theorem sorted_value_indices' (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem grouping_sorted' (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (fun i j => i.val ≤ j.val)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_value_indices' positions, List.map_map]

private theorem grouping_empty' (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem cap_frontier_positive' (groups : List Nat) (node height : Nat)
    (span : Opening.CapSpan node height) :
    ∀ n ∈ capFrontierNodes groups node height, 0 < n := by
  induction height generalizing node with
  | zero =>
    have positive := (cap_span_node node 0 span).1
    cases mark : capIsMarked groups node 0 <;> simp [capFrontierNodes, mark, positive]
  | succ height ih =>
    have positive := (cap_span_node node (height+1) span).1
    have ⟨left, right⟩ := cap_span_children node height span
    cases mark : capIsMarked groups node (height+1)
    · simp [capFrontierNodes, mark, positive]
    · intro n member
      simp only [capFrontierNodes, mark, ite_true, List.mem_append] at member
      exact member.elim (ih _ left n) (ih _ right n)

/-- The level-`l` sibling of a leaf is the mate leaf at level 0 and an internal node above. -/
theorem sibling_internal (index : Index) (level : Nat) (lo : 1 ≤ level) (hi : level < 16) :
    0 < (lowerNode index level ^^^ 1) ∧ (lowerNode index level ^^^ 1) < LENGTH := by
  have hL : LENGTH = 16777216 := rfl
  have hidx := index.isLt
  unfold lowerNode
  have p1 : 2 ≤ 2 ^ level := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ level := Nat.pow_le_pow_right (by decide) lo
  have p2 : 2 ^ level ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
  have upper : (LENGTH + index.val) / 2 ^ level < LENGTH := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    have : LENGTH * 2 ≤ LENGTH * 2 ^ level := Nat.mul_le_mul_left _ p1
    omega
  have lower : 512 ≤ (LENGTH + index.val) / 2 ^ level := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have : 512 * 2 ^ level ≤ 512 * 2 ^ 15 := Nat.mul_le_mul_left _ p2
    omega
  by_cases e : ((LENGTH + index.val) / 2 ^ level) % 2 = 0
  · rw [xor_one_even e]
    constructor <;> omega
  · rw [xor_one_odd (by omega)]; constructor <;> omega

theorem record_matches_on (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (heap : Nat → BitVec 256) (salts : CompleteSaltTape) (index : Index)
    (internal : ∀ node, 0 < node → node < LENGTH → trapdoorHeap (s := s) trapdoor node = heap node)
    (mate : trapdoorHeap (s := s) trapdoor (LENGTH + (index.val ^^^ 1)) = heap (LENGTH + (index.val ^^^ 1)))
    (salt : trapdoorSalt (s := s) trapdoor index = salts index) :
    Hybrid.record (trapdoorHeap (s := s) trapdoor) index (trapdoorSalt (s := s) trapdoor index) =
      Hybrid.record heap index (salts index) := by
  unfold Hybrid.record
  rw [salt]
  congr 1
  apply List.flatMap_congr
  intro level live
  have inside := List.mem_range.mp live
  by_cases zero : level = 0
  · subst zero
    simp only [Nat.pow_zero, Nat.div_one]
    rw [leaf_mate_node index.val index.isLt, mate]
  · have both := sibling_internal index level (by omega) inside
    have same := internal _ both.1 both.2
    simp only [lowerNode] at same
    rw [same]

/-- **The proof read from trapdoor′** equals the honest proof when trapdoor′ is right at every internal
node and, for each opened leaf, at its salt and its mate's leaf slot. -/
theorem proof_from_trapdoor_on (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (compress : Compression) (leaves : DigestTape) (salts : CompleteSaltTape)
    (internal : ∀ node, 0 < node → node < LENGTH →
      trapdoorHeap (s := s) trapdoor node = Hybrid.heap compress leaves node)
    (mates : ∀ i ∈ positions, trapdoorHeap (s := s) trapdoor (LENGTH + (i.val ^^^ 1)) =
      Hybrid.heap compress leaves (LENGTH + (i.val ^^^ 1)))
    (salt : ∀ i ∈ positions, trapdoorSalt (s := s) trapdoor i = salts i) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (Hybrid.builder compress positions (fun i => salts i.val) leaves).2 := by
  let heap := Hybrid.heap compress leaves
  unfold proofFromTrapdoor Hybrid.builder
  dsimp only
  congr 1
  · rw [← sorted_value_indices' positions, List.flatMap_map]
    apply List.flatMap_congr
    intro index _
    exact record_matches_on s trapdoor heap salts index.val internal (mates index.val index.property)
      (salt index.val index.property)
  · unfold frontierProof
    rw [← grouping_sorted' positions]
    by_cases empty : positions.card = 0
    · simp [openingNodes, empty, groupsBefore]
    · have someGroups : (groupsBefore positions positions.card).isEmpty = false := by
        cases h : (groupsBefore positions positions.card).isEmpty
        · rfl
        · exact False.elim (empty ((grouping_empty' positions).mp h))
      simp only [openingNodes, empty, someGroups, Bool.false_eq_true, ite_false]
      apply List.flatMap_congr
      intro node member
      have small := cap_frontier_nodes_small _ 1 8 cap_span_root node member
      have capacity : 512 < LENGTH := by decide
      rw [internal _ (cap_frontier_positive' _ 1 8 cap_span_root node member) (small.trans capacity)]

end TwoPermutationPrototype.PackedOpening
