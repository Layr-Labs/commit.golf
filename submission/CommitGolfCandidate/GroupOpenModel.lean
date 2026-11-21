import CommitGolfCandidate.GroupOpenMemory
import CommitGolfCandidate.QuartetConcrete
import CommitGolfCandidate.K3OpenPack238
import CommitGolfCandidate.K3OpenCapBytes
import CommitGolfCandidate.TwoPermutationOpeningProofBytes

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open Opening (groupsBefore lowerNode trapdoorHeap openingNodes)
open Sampling.Quartet (upperHeap leafAt builder)
set_option maxRecDepth 8192

def trapdoorSalt {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (index : Index) : BitVec 128 :=
  t.extractLsb' (8*(288*LENGTH+16*index.val)) 128

/-- Leaf digest `index` where the writer reads it: in the block the prefix rebuilt from the group reply
(`0^72 ‖ d0..d3` at trapdoor offset `32 L + 512 + 1024 ⌊index/4⌋`). -/
def trapdoorLeaf {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (index : Nat) : BitVec 256 :=
  t.extractLsb' (8*(32*LENGTH + 512 + 1024*(index/4) + 72 + 32*(index%4))) 256

/-- The level-22 node of the sibling quartet of `index`'s quartet where the writer reads it: in the commit's group
replies (`quadAddress`), not in the heap. -/
def trapdoorQuad {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (index : Index) : BitVec 256 :=
  t.extractLsb' (8*(quadAddress index.val-trapdoorBase)) 256

/-- One record as the writer leaves it: salt, three mates, levels 0..5 (32, 32, then 30 bytes; level 0 is the
sibling quartet's node `quad`), and the packed levels 6..13 in the folded form. -/
def physicalRecord (leaf heap : Nat → BitVec 256) (quad : BitVec 256) (index : Index) (salt : BitVec 128) : Proof :=
  saltBytes salt ++ ([1,2,3] : List Nat).flatMap (fun j => digestBytes (leaf (index.val ^^^ j))) ++
    (List.range 6).flatMap (fun l => proofDigestBytes (2 ≤ l) (if l = 0 then quad else heap (upperNode index l ^^^ 1))) ++
    foldPack8 (fun k => heap (upperNode index (6+k) ^^^ 1))

def proofFromTrapdoor {s : Submission} (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (fun i => physicalRecord (trapdoorLeaf (s:=s) t) (trapdoorHeap (s:=s) t)
    (trapdoorQuad (s:=s) t i) i (trapdoorSalt (s:=s) t i)) ++
  foldNodes ((openingNodes positions).map (trapdoorHeap (s:=s) t))

theorem upper_sibling_bound (i : Index) (l : Nat) :
    upperNode i l ^^^ 1 < 2*(LENGTH/4) := by
  have bound : 4194304+i.val/4 < 2^23 := by have ix : i.val<16777216 := i.isLt; omega
  have n : upperNode i l < 2^23 := by
    rw [upper_node_heap_index]
    exact (Nat.div_le_self _ _).trans_lt bound
  exact Nat.xor_lt_two_pow n (show (1:Nat) < 2^23 by decide)


/-! ### The writer's proof is the builder's proof -/

open Opening (cap_frontier_nodes_small cap_span_root cap_span_node cap_span_children)
open Sampling.Quartet (openingRecord packEight packNodes packedSlot frontierProof238 upper_heap_parent)

private theorem sorted_values (positions : Positions) :
    (positions.attach.sort (· ≤ ·)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i ≤ j)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem groups_sorted (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (· ≤ ·)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_values positions, List.map_map]

private theorem groups_empty (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem frontier_positive (groups : List Nat) (node height : Nat)
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

/-- `n ^^^ j` for `j < 2^k` only changes the low `k` bits. -/
private theorem xor_split (n j k : Nat) (small : j < 2^k) :
    n ^^^ j = 2^k*(n/2^k) + (n % 2^k ^^^ j) := by
  have g : (n ^^^ j)/2^k = n/2^k := by
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib]
    have zero : j >>> k = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt small
    simp [zero]
  have p : (n ^^^ j)%2^k = n%2^k ^^^ j := by
    rw [Nat.xor_mod_two_pow, Nat.mod_eq_of_lt small]
  have split := Nat.div_add_mod (n ^^^ j) (2^k)
  rw [g, p] at split
  omega

private theorem sibling_range (u : Nat) (pos : 2 ≤ u) : 0 < u ^^^ 1 ∧ u ^^^ 1 ≤ u+1 := by
  have split := xor_split u 1 1 (by decide)
  have low : u % 2^1 ^^^ 1 < 2^1 := Nat.xor_lt_two_pow (by rw [Nat.pow_one]; omega) (by decide)
  simp only [Nat.pow_one] at split low
  rw [split]
  omega

private theorem pad238_high (x : BitVec 256) : (pad238 x).extractLsb' 238 18 = 0 := by
  unfold pad238
  exact BitVec.extractLsb'_append_eq_left

/-- Every stored node of depth 0..16 has bits `238..255` zero. -/
theorem upper_heap_high (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (n : Nat) (pos : 0 < n) (small : n < 2^17) :
    (upperHeap lookup compress leaves n).extractLsb' 238 18 = 0 := by
  have stored := (upper_heap_parent lookup compress leaves n pos (by omega)).trans (node_keep_238 small _)
  rw [stored]
  exact pad238_high _

/-- The sibling at path level `l = 6..12` is a depth-16..10 node. -/
private theorem packed_sibling_range (i : Index) (k : Nat) (hk : k < 7) :
    0 < upperNode i (6+k) ^^^ 1 ∧ upperNode i (6+k) ^^^ 1 < 2^17 := by
  have hi : i.val < 16777216 := i.isLt
  rw [upper_node_heap_index]
  have p1 : 2^(6+k) ≤ 4096 := (Nat.pow_le_pow_right (by decide) (show 6+k ≤ 12 by omega)).trans (by decide)
  have p0 : 64 ≤ 2^(6+k) := (show 64 ≤ 2^6 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have range : 512 ≤ (4194304+i.val/4)/2^(6+k) ∧ (4194304+i.val/4)/2^(6+k) < 131072 := by
    constructor
    · rw [Nat.le_div_iff_mul_le (by positivity)]; omega
    · rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have side := sibling_range _ (show 2 ≤ (4194304+i.val/4)/2^(6+k) by omega)
  refine ⟨side.1, ?_⟩
  exact Nat.xor_lt_two_pow (n := 17) (by simpa using range.2) (by decide)

private theorem fold_pack8_congr (s s' : Nat → BitVec 256) (same : ∀ k < 8, s k = s' k) :
    foldPack8 s = foldPack8 s' := by
  unfold foldPack8
  rw [same 7 (by decide)]
  congr 1
  apply List.flatMap_congr
  intro k member
  rw [same k (by simp at member; omega)]

private theorem range_getD (values : List (BitVec 256)) (long : 8 ≤ values.length) :
    (List.range 8).map (fun k => values.getD k 0) = values.take 8 := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getElem?_eq_getElem (show k < values.length by omega)]

/-- With bits `238..255` zero, the machine's cap bytes are `packNodes`. -/
theorem fold_nodes_pack : ∀ (values : List (BitVec 256)), (∀ v ∈ values, v.extractLsb' 238 18 = 0) →
    foldNodes values = packNodes values
  | values, high => by
    rw [foldNodes, packNodes]
    by_cases long : 8 ≤ values.length
    · rw [if_pos long, if_pos long]
      have top : ∀ k < 7, (values.getD k 0).extractLsb' 238 18 = 0 := by
        intro k hk
        rw [List.getD_eq_getElem _ _ (show k < values.length by omega)]
        exact high _ (List.getElem_mem _)
      rw [fold_pack8 _ top, range_getD values long,
        fold_nodes_pack (values.drop 8) (fun v member => high v (List.mem_of_mem_drop member))]
    · rw [if_neg long, if_neg long]
      apply List.flatMap_congr
      intro v member
      exact partial_slot v (high v member)
termination_by values => values.length
decreasing_by simp only [List.length_drop]; omega

private theorem record_matches (s : Submission) (t : BitVec (8*s.sizes.trapdoor))
    (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape)
    (index : Index) (salt : BitVec 128)
    (digest : ∀ l < 14, 0 < l → trapdoorHeap (s:=s) t (upperNode index l ^^^ 1) =
      upperHeap lookup compress leaves (((4194304 + (index.val/4 ^^^ 1)) / 2^l) ^^^ 1))
    (quad : trapdoorQuad (s:=s) t index =
      upperHeap lookup compress leaves (((4194304 + (index.val/4 ^^^ 1)) / 2^0) ^^^ 1))
    (leaf : ∀ j, 0 < j → j < 4 → trapdoorLeaf (s:=s) t (index.val ^^^ j) = leafAt leaves (index.val ^^^ j))
    (stored : trapdoorSalt (s:=s) t index = salt) :
    physicalRecord (trapdoorLeaf (s:=s) t) (trapdoorHeap (s:=s) t) (trapdoorQuad (s:=s) t index) index
        (trapdoorSalt (s:=s) t index) =
      openingRecord leaves (upperHeap lookup compress leaves) index salt := by
  have mid : (List.range 6).flatMap (fun l => proofDigestBytes (2 ≤ l)
        (if l = 0 then trapdoorQuad (s:=s) t index else trapdoorHeap (s:=s) t (upperNode index l ^^^ 1))) =
      (List.range 6).flatMap (fun level => proofDigestBytes (2 ≤ level)
        (upperHeap lookup compress leaves ((((4194304 + (index.val/4 ^^^ 1)) / 2^level)) ^^^ 1))) := by
    apply List.flatMap_congr
    intro l member
    have level := List.mem_range.mp member
    by_cases zero : l = 0
    · subst zero
      rw [if_pos rfl, quad]
    · rw [if_neg zero, digest l (by omega) (by omega)]
  have mates : ([1,2,3] : List Nat).flatMap (fun j => digestBytes (trapdoorLeaf (s:=s) t (index.val ^^^ j))) =
      ([1,2,3] : List Nat).flatMap (fun j => digestBytes (leafAt leaves (index.val ^^^ j))) := by
    apply List.flatMap_congr
    intro j member
    have small : 0 < j ∧ j < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    rw [leaf j small.1 small.2]
  have same : ∀ k < 8, trapdoorHeap (s:=s) t (upperNode index (6+k) ^^^ 1) =
      upperHeap lookup compress leaves (upperNode index (6+k) ^^^ 1) := fun k hk => by
    rw [digest (6+k) (by omega) (by omega), Sampling.Quartet.flip_start_shift _ _ (by omega), upper_node_heap_index]
  have packed : foldPack8 (fun k => trapdoorHeap (s:=s) t (upperNode index (6+k) ^^^ 1)) =
      packEight ((List.range 8).map (fun k => upperHeap lookup compress leaves ((((4194304 + index.val/4) / 2^(6+k))) ^^^ 1))) := by
    rw [fold_pack8_congr _ _ same]
    rw [fold_pack8 _ (fun k hk => by
      have range := packed_sibling_range index k hk
      exact upper_heap_high lookup compress leaves _ range.1 range.2)]
    congr 1
    apply List.map_congr_left
    intro k _
    rw [upper_node_heap_index]
  unfold physicalRecord openingRecord
  rw [stored, mates, mid, packed]

/-- The proof the opener writes from a trapdoor that agrees with the honest heap on the nodes a record
and the cap read is the builder's proof. -/
theorem proof_from_trapdoor_matches (s : Submission) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape) (salts : CompleteSaltTape)
    (digest : ∀ i ∈ positions, ∀ l < 14, 0 < l → trapdoorHeap (s:=s) t (upperNode i l ^^^ 1) =
      upperHeap lookup compress leaves (((4194304 + (i.val/4 ^^^ 1)) / 2^l) ^^^ 1))
    (quad : ∀ i ∈ positions, trapdoorQuad (s:=s) t i =
      upperHeap lookup compress leaves (((4194304 + (i.val/4 ^^^ 1)) / 2^0) ^^^ 1))
    (cap : ∀ n ∈ openingNodes positions, trapdoorHeap (s:=s) t n = upperHeap lookup compress leaves n)
    (leaf : ∀ i ∈ positions, ∀ j, 0 < j → j < 4 → trapdoorLeaf (s:=s) t (i.val ^^^ j) = leafAt leaves (i.val ^^^ j))
    (salt : ∀ i ∈ positions, trapdoorSalt (s:=s) t i = salts i) :
    proofFromTrapdoor (s:=s) t positions = (builder lookup compress positions (fun i => salts i.val) leaves).2 := by
  unfold proofFromTrapdoor builder
  dsimp only
  congr 1
  · rw [← sorted_values positions, List.flatMap_map]
    apply List.flatMap_congr
    intro index _
    exact record_matches s t lookup compress leaves index.val (salts index.val)
      (digest index.val index.property) (quad index.val index.property) (leaf index.val index.property)
      (salt index.val index.property)
  · unfold frontierProof238
    rw [← groups_sorted positions]
    by_cases empty : positions.card = 0
    · have none : (groupsBefore positions positions.card).isEmpty = true := (groups_empty positions).mpr empty
      have noNodes : openingNodes positions = [] := by simp [openingNodes, empty]
      rw [if_pos none, noNodes, List.map_nil, foldNodes]
      simp
    · have someGroups : (groupsBefore positions positions.card).isEmpty = false := by
        cases h : (groupsBefore positions positions.card).isEmpty
        · rfl
        · exact False.elim (empty ((groups_empty positions).mp h))
      have nodes : openingNodes positions = capFrontierNodes (groupsBefore positions positions.card) 1 8 := by
        simp only [openingNodes, empty, ite_false]
      rw [someGroups]
      simp only [Bool.false_eq_true, ite_false]
      rw [List.map_congr_left (fun n member => cap n member), nodes]
      apply fold_nodes_pack
      intro v member
      obtain ⟨n, inside, rfl⟩ := List.mem_map.mp member
      exact upper_heap_high lookup compress leaves n
        (frontier_positive _ 1 8 cap_span_root n inside)
        ((cap_frontier_nodes_small _ 1 8 cap_span_root n inside).trans (by decide))

/-- O2's shape (what the K3-lite virtual trapdoor provides). The level-0 sibling the writer reads for a position of
group `g` (`trapdoorQuad`, the commit's node of group `g ^^^ 1`) must be the builder's heap node `2^22 + g`. -/
theorem proof_from_trapdoor_matches_virtual (s : Submission) (t : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (lookup : Nat → BitVec 1024 → BitVec 256) (compress : Compression) (leaves : DigestTape) (salts : CompleteSaltTape)
    (heap : ∀ n, 0 < n → n < 4194304 → trapdoorHeap (s:=s) t n = upperHeap lookup compress leaves n)
    (sibling : ∀ i ∈ positions, trapdoorQuad (s:=s) t i = upperHeap lookup compress leaves (4194304 + i.val/4))
    (leaf : ∀ i ∈ positions, ∀ j < 4, trapdoorLeaf (s:=s) t (4*(i.val/4)+j) = leafAt leaves (4*(i.val/4)+j))
    (salt : ∀ i ∈ positions, trapdoorSalt (s:=s) t i = salts i) :
    proofFromTrapdoor (s:=s) t positions = (builder lookup compress positions (fun i => salts i.val) leaves).2 := by
  have flip : ∀ g : Nat, (4194304 + g) ^^^ 1 = 4194304 + (g ^^^ 1) := by
    intro g
    have outer := xor_split (4194304+g) 1 1 (by decide)
    have inner := xor_split g 1 1 (by decide)
    have parity : (4194304+g) % 2^1 = g % 2^1 := by omega
    rw [parity] at outer
    rw [outer, inner]
    omega
  apply proof_from_trapdoor_matches s t positions lookup compress leaves salts _ _ _ _ salt
  · intro i member l level nonzero
    have hi : i.val < 16777216 := i.isLt
    have zero : l ≠ 0 := by omega
    · rw [Sampling.Quartet.flip_start_shift _ _ (by omega), upper_node_heap_index]
      have p1 : 2^l ≤ 8192 := (Nat.pow_le_pow_right (by decide) (show l ≤ 13 by omega)).trans (by decide)
      have p0 : 2 ≤ 2^l := (show 2 ≤ 2^1 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega))
      have range : 2 ≤ (4194304+i.val/4)/2^l ∧ (4194304+i.val/4)/2^l < 4194304 := by
        constructor
        · rw [Nat.le_div_iff_mul_le (by positivity)]; omega
        · rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
      have side := sibling_range _ range.1
      exact heap _ side.1 (Nat.xor_lt_two_pow (n := 22) (by simpa using range.2) (by decide))
  · intro i member
    rw [Nat.pow_zero, Nat.div_one, flip, Sampling.Quartet.xor_one_xor_one]
    exact sibling i member
  · intro n member
    have nonempty : positions.card ≠ 0 := by
      intro empty
      simp [openingNodes, empty] at member
    have inside : n ∈ capFrontierNodes (groupsBefore positions positions.card) 1 8 := by
      simpa only [openingNodes, nonempty, ite_false] using member
    exact heap n (frontier_positive _ 1 8 cap_span_root n inside)
      ((cap_frontier_nodes_small _ 1 8 cap_span_root n inside).trans (by decide))
  · intro i member j pos small
    have slot := xor_split i.val j 2 (by simpa using small)
    have low : i.val % 2^2 ^^^ j < 4 := Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by simpa using small)
    have four : (2:Nat)^2 = 4 := by decide
    rw [four] at slot low
    rw [slot]
    exact leaf i member _ low

end TwoPermutationPrototype.GroupedOpening
