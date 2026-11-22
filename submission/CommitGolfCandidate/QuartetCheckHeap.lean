import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.TwoPermutationOpeningMarks
import CommitGolfCandidate.TwoPermutationCheckerPaths
import CommitGolfCandidate.ProjectedCompression

/-! Heap facts for the Quartet checker: the honest upper heap, its parent relation, and the
coincidence of Quartet's upper nodes with cursor43's binary heap numbering two levels up. -/

namespace TwoPermutationPrototype.QuartetCheck
open CommitGolf CommitGolfCandidate CommitGolfCandidate.ShortTree TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (upperHeap quartetPayload leafAt)

set_option autoImplicit false

theorem upper_heap_parent (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (below : node < 4194304) :
    upperHeap lookup compress leaves node =
      projectInternal true compress (upperHeap lookup compress leaves (2*node+1) ++ upperHeap lookup compress leaves (2*node)) := by
  unfold upperHeap
  exact reference_heap_parent _ _ _ _ positive below

theorem upper_heap_leaf (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (group : Nat) (inside : group < 4194304) :
    upperHeap lookup compress leaves (4194304+group) = lookup (quartetPayload leaves group) := by
  unfold upperHeap
  exact reference_heap_leaf _ _ _ _ inside

/-- One authenticated step of the honest upper heap, in the checker's projected form. -/
theorem upper_heap_climb (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 2 ≤ node) (bounded : node < 8388608) :
    let heap := upperHeap lookup compress leaves
    padLow (compress (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2) := by
  let heap := upperHeap lookup compress leaves
  change padLow (compress (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2)
  have parent := upper_heap_parent lookup compress leaves (node/2) (by omega) (by omega)
  change heap (node/2) = padLow (compress (heap (2*(node/2)+1) ++ heap (2*(node/2)))) at parent
  rw [parent]
  by_cases even : node % 2 = 0
  · rw [pathPair, ite_eq_left even, Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2*(node/2)+1 = node+1 by omega,show 2*(node/2) = node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair, ite_eq_right even, Nat.xor_one_of_odd odd]
    rw [show 2*(node/2)+1 = node by omega,show 2*(node/2) = node-1 by omega]

/-- Internal digests are projected: their two top bytes are zero. -/
theorem upper_heap_projected (lookup : BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (internal : node < 4194304) :
    (0#16) ++ (upperHeap lookup compress leaves node).extractLsb' 0 240 = upperHeap lookup compress leaves node := by
  rw [upper_heap_parent lookup compress leaves node positive internal]
  simp [projectInternal]
  rw [BitVec.extractLsb'_append_eq_right]

/-- Quartet's upper level `level` is cursor43's binary level `level+2`. -/
theorem lower_node_shift (index : Index) (level : Nat) :
    Opening.lowerNode index (level+2) = (4194304 + index.val/4) / 2^level := by
  unfold Opening.lowerNode
  rw [show level+2 = 2+level by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  congr 1
  change (16777216 + index.val)/4 = 4194304 + index.val/4
  omega

theorem lower_node_two (index : Index) : Opening.lowerNode index 2 = 4194304 + index.val/4 := by
  simpa using lower_node_shift index 0

theorem lower_node_upper_bounds (index : Index) (level : Nat) (within : level < 14) :
    2 ≤ Opening.lowerNode index (level+2) ∧ Opening.lowerNode index (level+2) < 8388608 := by
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  rw [lower_node_shift]
  have scale : (2:Nat)^level ≤ 8192 :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show level ≤ 13 by omega)).trans (by decide)
  constructor
  · apply (Nat.le_div_iff_mul_le (by positivity : 0 < (2:Nat)^level)).mpr
    omega
  · exact (Nat.div_le_self _ _).trans_lt (by omega)

theorem lower_node_sibling_internal (index : Index) (level : Nat) (later : 0 < level) (within : level < 14) :
    0 < Opening.lowerNode index (level+2) ^^^ 1 ∧ Opening.lowerNode index (level+2) ^^^ 1 < 4194304 := by
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  let node := Opening.lowerNode index (level+2)
  have scale : 2 ≤ (2:Nat)^level := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show 1 ≤ level by omega)
  have lo : 2 ≤ node := (lower_node_upper_bounds index level within).1
  have hi : node < 4194304 := by
    change Opening.lowerNode index (level+2) < 4194304
    rw [lower_node_shift]
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2:Nat)^level)).mpr
    have fit : (4194304:Nat)*2 ≤ 4194304*2^level := Nat.mul_le_mul_left _ scale
    omega
  change 0 < node ^^^ 1 ∧ node ^^^ 1 < 4194304
  by_cases parity : node % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr parity)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

end TwoPermutationPrototype.QuartetCheck
