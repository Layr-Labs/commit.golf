import CommitGolfCandidate.QuartetRVRecordData
import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.TwoPermutationOpeningProofBytes

namespace TwoPermutationPrototype.QuartetRV
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open Opening (groupsBefore lower_swap_bound lowerNode trapdoorHeap openingNodes
  cap_frontier_nodes_small cap_span_root cap_span_node cap_span_children)
open Sampling.Quartet (upperHeap openingRecord leafAt builder)
set_option maxRecDepth 8192

def trapdoorSalt {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (index : Index) : BitVec 128 :=
  t.extractLsb' (8*(288*LENGTH+16*index.val)) 128

def trapdoorLeaf {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (index : Nat) : BitVec 256 :=
  t.extractLsb' (8*(32*LENGTH + 1024*(index/4) + 72 + 32*(index%4))) 256

def physicalRecord (leaf heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) : Proof :=
  saltBytes salt ++ ([1,2,3] : List Nat).flatMap (fun j => digestBytes (leaf (index.val ^^^ j))) ++
    (List.range 14).flatMap (fun l => proofDigestBytes (l != 0) (heap (upperNode index l ^^^ 1)))

def proofFromTrapdoor {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (fun i => physicalRecord (trapdoorLeaf (s:=s) t) (trapdoorHeap (s:=s) t)
    i (trapdoorSalt (s:=s) t i)) ++
  (openingNodes positions).flatMap (fun n => proofDigestBytes true (trapdoorHeap (s:=s) t n))
private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (· ≤ ·)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i ≤ j)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem grouping_sorted (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (· ≤ ·)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_value_indices positions, List.map_map]

private theorem grouping_empty (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem lower_sibling_positive (index : Index) (level : Nat) (bound : level < 16) :
    0 < (lowerNode index level ^^^ 1) := by
  have depth : 2^level ≤ 2^16 := Nat.pow_le_pow_right (by decide) (by omega)
  have leafBound : 2*2^level ≤ LENGTH+index.val := by
    have room : 2*2^16 ≤ LENGTH := by decide
    omega
  have above : 2 ≤ lowerNode index level := by
    unfold lowerNode
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr leafBound
  by_contra! zero
  have emptied : (lowerNode index level ^^^ 1) = 0 := by omega
  have collapsed := congrArg (fun n : Nat => n ^^^ 1) emptied
  simp [Nat.xor_assoc] at collapsed
  omega

private theorem cap_frontier_positive (groups : List Nat) (node height : Nat)
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


theorem upper_sibling_bound (i : Index) (l : Nat) :
    upperNode i l ^^^ 1 < 2*(LENGTH/4) := by
  have bound : 4194304+i.val/4 < 2^23 := by have ix : i.val<16777216 := i.isLt; omega
  have n : upperNode i l < 2^23 := by
    rw [upper_node_heap_index]
    exact (Nat.div_le_self _ _).trans_lt bound
  exact Nat.xor_lt_two_pow n (show (1:Nat) < 2^23 by decide)

end TwoPermutationPrototype.QuartetRV
