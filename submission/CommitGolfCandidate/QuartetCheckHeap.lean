import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.K3GQModel
import CommitGolfCandidate.TwoPermutationOpeningMarks
import CommitGolfCandidate.TwoPermutationCheckerPaths
import CommitGolfCandidate.ProjectedCompression

/-! Heap facts for the Quartet checker: the honest upper heap, its parent relation, and the
coincidence of Quartet's upper nodes with cursor43's binary heap numbering two levels up. -/

namespace TwoPermutationPrototype.QuartetCheck
open CommitGolf CommitGolfCandidate CommitGolfCandidate.ShortTree TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (upperHeap quartetPayload leafAt)

set_option autoImplicit false

theorem upper_heap_parent (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (below : node < 4194304) :
    upperHeap lookup compress leaves node =
      nodeKeep node (compress (upperHeap lookup compress leaves (2*node+1) ++ upperHeap lookup compress leaves (2*node))) :=
  Sampling.Quartet.upper_heap_parent lookup compress leaves node positive below

theorem upper_heap_leaf (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (group : Nat) (inside : group < 4194304) :
    upperHeap lookup compress leaves (4194304+group) = lookup (group ^^^ 1) (quartetPayload leaves (group ^^^ 1)) :=
  Sampling.Quartet.upper_heap_leaf lookup compress leaves group inside

/-- Group `g`'s node sits at heap node `2^22 + (g ^^^ 1)`. -/
theorem upper_heap_leaf_flip (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression)
    (leaves : DigestTape) (group : Nat) (inside : group < 4194304) :
    upperHeap lookup compress leaves (4194304 + (group ^^^ 1)) = lookup group (quartetPayload leaves group) :=
  Sampling.Quartet.upper_heap_leaf_flip lookup compress leaves group inside

/-- One authenticated step of the honest upper heap, in the checker's level-aware form. -/
theorem upper_heap_climb (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 2 ≤ node) (bounded : node < 8388608) :
    let heap := upperHeap lookup compress leaves
    nodeKeep (node/2) (compress (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2) := by
  let heap := upperHeap lookup compress leaves
  change nodeKeep (node/2) (compress (pathPair node (heap node) (heap (node ^^^ 1)))) = heap (node/2)
  have parent := upper_heap_parent lookup compress leaves (node/2) (by omega) (by omega)
  change heap (node/2) = nodeKeep (node/2) (compress (heap (2*(node/2)+1) ++ heap (2*(node/2)))) at parent
  rw [parent]
  by_cases even : node % 2 = 0
  · rw [pathPair, ite_eq_left even, Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2*(node/2)+1 = node+1 by omega,show 2*(node/2) = node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair, ite_eq_right even, Nat.xor_one_of_odd odd]
    rw [show 2*(node/2)+1 = node by omega,show 2*(node/2) = node-1 by omega]

/-- Internal digests below level 21 are projected (240 or 238 kept bits): their two top bytes are zero. -/
theorem upper_heap_projected (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (internal : node < 2097152) :
    (0#16) ++ (upperHeap lookup compress leaves node).extractLsb' 0 240 = upperHeap lookup compress leaves node := by
  rw [upper_heap_parent lookup compress leaves node positive (by omega)]
  generalize compress (upperHeap lookup compress leaves (2*node+1) ++ upperHeap lookup compress leaves (2*node)) = x
  by_cases t238 : node < 2^17
  · rw [show nodeKeep node x = pad238 x from node_keep_238 t238 x]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [pad238, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases low : i < 238
    · simp [low, show i < 240 by omega]
    · by_cases mid : i < 240
      · simp [low, mid]
      · simp [low, mid]
  · rw [show nodeKeep node x = padLow x from node_keep_240 (by omega) (by omega) x]
    unfold padLow
    rw [BitVec.extractLsb'_append_eq_right]
    try rfl

/-- Internal digests below level 17 keep 238 bits. -/
theorem upper_heap_projected238 (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (internal : node < 2^17) :
    pad238 (upperHeap lookup compress leaves node) = upperHeap lookup compress leaves node := by
  rw [upper_heap_parent lookup compress leaves node positive (by omega)]
  generalize compress (upperHeap lookup compress leaves (2*node+1) ++ upperHeap lookup compress leaves (2*node)) = x
  rw [show nodeKeep node x = pad238 x from node_keep_238 internal x]
  unfold pad238
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

/-! ### The checker's path index

The check image flips bit 2 of the index (`xori x6,x6,4`) before the quartet's parity test and heap index, so
its lower loop runs at `flipIndex i = i ^^^ 4`: heap node `2^22 + (⌊i/4⌋ ^^^ 1)` at loop level 0, and the
same ancestors as `i` from loop level 1 on. -/

/-- The index whose loop path the checker walks for position `index`. -/
def flipIndex (index : Index) : Index :=
  ⟨index.val ^^^ 4, by
    have bound : index.val < 2^24 := index.isLt
    exact Nat.xor_lt_two_pow bound (by decide)⟩

theorem flip_index_val (index : Index) : (flipIndex index).val = index.val ^^^ 4 := rfl

theorem flip_index_cases (index : Index) :
    (flipIndex index).val = if index.val / 4 % 2 = 0 then index.val + 4 else index.val - 4 :=
  Sampling.Quartet.xor_four_cases index.val

theorem flip_index_group (index : Index) : (flipIndex index).val / 4 = index.val / 4 ^^^ 1 :=
  Sampling.Quartet.xor_four_div index.val

theorem flip_index_mod (index : Index) : (flipIndex index).val % 4 = index.val % 4 := by
  rw [flip_index_cases]; split <;> omega

theorem lower_node_two_flip (index : Index) :
    Opening.lowerNode (flipIndex index) 2 = 4194304 + (index.val/4 ^^^ 1) := by
  rw [lower_node_two, flip_index_group]

/-- From loop level 1 on (binary level 3) the flipped path and the plain one coincide. -/
theorem lower_node_flip (index : Index) (level : Nat) (later : 3 ≤ level) :
    Opening.lowerNode (flipIndex index) level = Opening.lowerNode index level := by
  obtain ⟨l, rfl⟩ : ∃ l, level = l + 3 := ⟨level - 3, by omega⟩
  unfold Opening.lowerNode
  have eight : (2:Nat)^(l+3) = 8 * 2^l := by rw [Nat.pow_add, Nat.mul_comm] <;> norm_num
  have octet : (LENGTH + (flipIndex index).val) / 8 = (LENGTH + index.val) / 8 := by
    rw [flip_index_cases]
    change (16777216 + _) / 8 = (16777216 + index.val) / 8
    split <;> omega
  rw [eight, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, octet]

theorem lower_node_shift_flip (index : Index) (level : Nat) :
    Opening.lowerNode (flipIndex index) (level+2) = (4194304 + (index.val/4 ^^^ 1)) / 2^level := by
  rw [lower_node_shift, flip_index_group]

theorem cap_group_flip (index : Index) : Sampling.capGroup (flipIndex index) = Sampling.capGroup index := by
  unfold Sampling.capGroup
  rw [flip_index_cases]
  change (16777216 + _) / 65536 = (16777216 + index.val) / 65536
  split <;> omega

theorem flip_flip_index (index : Index) : flipIndex (flipIndex index) = index := by
  apply Fin.ext
  change index.val ^^^ 4 ^^^ 4 = index.val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

end TwoPermutationPrototype.QuartetCheck
