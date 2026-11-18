import CommitGolfCandidate.QOpeningProofBytes
import CommitGolfCandidate.TwoPermutationQuadSpec

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open QOpening (groupsBefore trapdoorHeap trapdoorSalt openingNodes cap_frontier_nodes_small cap_span_root cap_span_node cap_span_children)

/-- Leaf digests read back from the quad leaf-group slots of the trapdoor. -/
def trapdoorLeaves {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor)) : DigestTape :=
  fun i => quadTrapdoorLeaf trapdoor i

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (fun i => quadLowerRecord (trapdoorHeap (s := s) trapdoor)
    (trapdoorLeaves (s := s) trapdoor) i (trapdoorSalt (s := s) trapdoor i)) ++
    (openingNodes positions).flatMap (fun node => proofDigestBytes true (trapdoorHeap (s := s) trapdoor node))

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem grouping_sorted (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (fun i j => i.val ≤ j.val)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_value_indices positions, List.map_map]

private theorem grouping_empty (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem xor_one_positive (x : Nat) (big : 2 ≤ x) : 0 < x ^^^ 1 := by
  by_contra! zero
  have emptied : x ^^^ 1 = 0 := by omega
  have collapsed := congrArg (fun n : Nat => n ^^^ 1) emptied
  simp [Nat.xor_assoc] at collapsed
  omega

private theorem xor_one_small (x : Nat) (small : x < LENGTH/2) : x ^^^ 1 < LENGTH/2 := by
  have half : LENGTH/2 = 2^23 := rfl
  rw [half] at small ⊢
  exact Nat.xor_lt_two_pow small (by decide)

private theorem quad_node_range (index : Index) :
    2 ≤ (LENGTH+index.val)/4 ∧ (LENGTH+index.val)/4 < LENGTH/2 := by
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  omega

private theorem binary_node_range (index : Index) (j : Nat) (hj : j < 13) :
    2 ≤ (LENGTH+index.val)/2^(j+3) ∧ (LENGTH+index.val)/2^(j+3) < LENGTH/2 := by
  have bound := index.isLt
  have hL : LENGTH = 16777216 := rfl
  interval_cases j <;> simp only [Nat.reduceAdd, Nat.reducePow] <;> omega

private theorem cap_frontier_positive (groups : List Nat) (node height : Nat)
    (span : QOpening.CapSpan node height) :
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

private theorem lower_record_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (heap : Nat → BitVec 256) (leaves : DigestTape) (salts : CompleteSaltTape) (index : Index)
    (digest : ∀ node, 0<node → node<LENGTH/2 → trapdoorHeap (s := s) trapdoor node = heap node)
    (leaf : ∀ i, quadTrapdoorLeaf trapdoor i = leaves i)
    (salt : ∀ i, trapdoorSalt (s := s) trapdoor i = salts i) :
    quadLowerRecord (trapdoorHeap (s := s) trapdoor) (trapdoorLeaves (s := s) trapdoor) index
        (trapdoorSalt (s := s) trapdoor index) =
      quadLowerRecord heap leaves index (salts index) := by
  have tape : trapdoorLeaves (s := s) trapdoor = leaves := funext leaf
  have quadRange := quad_node_range index
  have quadSib := digest _ (xor_one_positive _ quadRange.1) (xor_one_small _ quadRange.2)
  unfold quadLowerRecord
  rw [salt, tape, quadSib]
  congr 1
  apply List.flatMap_congr
  intro j live
  have range := binary_node_range index j (List.mem_range.mp live)
  rw [digest _ (xor_one_positive _ range.1) (xor_one_small _ range.2)]

/-- The pure transcript reconstructed from the concrete trapdoor slices agrees
with the reference transcript for any heap and nonce tape stored by commit. -/
theorem proof_from_trapdoor_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (salts : CompleteSaltTape)
    (digest : ∀ node, 0<node → node<LENGTH/2 →
      trapdoorHeap (s := s) trapdoor node = quadHeap compress quad leaves node)
    (leaf : ∀ i, quadTrapdoorLeaf trapdoor i = leaves i)
    (salt : ∀ index, trapdoorSalt (s := s) trapdoor index = salts index) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (quadTranscriptBuilder compress quad positions (fun i => salts i.val) leaves).2 := by
  let heap := quadHeap compress quad leaves
  unfold proofFromTrapdoor quadTranscriptBuilder
  dsimp only
  congr 1
  · rw [← sorted_value_indices positions, List.flatMap_map]
    apply List.flatMap_congr
    intro index _
    exact lower_record_matches s trapdoor heap leaves salts index.val digest leaf salt
  · unfold frontierProof
    rw [← grouping_sorted positions]
    by_cases empty : positions.card = 0
    · simp [openingNodes, empty, groupsBefore]
    · have someGroups : (groupsBefore positions positions.card).isEmpty = false := by
        cases h : (groupsBefore positions positions.card).isEmpty
        · rfl
        · exact False.elim (empty ((grouping_empty positions).mp h))
      simp only [openingNodes, empty, someGroups, Bool.false_eq_true, ite_false]
      apply List.flatMap_congr
      intro node member
      have small := cap_frontier_nodes_small _ 1 8 cap_span_root node member
      have capacity : 512 < LENGTH/2 := by decide
      rw [digest _ (cap_frontier_positive _ 1 8 cap_span_root node member) (small.trans capacity)]

end TwoPermutationPrototype.QuadOpening
