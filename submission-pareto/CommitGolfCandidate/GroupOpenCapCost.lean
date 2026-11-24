import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule
import CommitGolfCandidate.K3OpenCapBytes
import CommitGolfCandidate.GroupOpenCapChunkFrontier

namespace TwoPermutationPrototype.GroupedOpening
open TwoPermutationPrototype.Sampling

/-- Reference subtree charge before the destination-dependent copy savings. A marked internal node costs
14: the lookup and descent (7), the step across to its right child (3: parity test and row 660) and the
climb back from it (4: parity test, `srli`, `bne`). The root's last climb leaves through the `jal` at 705,
charged as one extra cycle by `cap_root`. -/
def capSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 37
  | height+1 =>
    if capIsMarked groups node (height+1) then
      14 + capSubtreeCycles groups (2*node) height + capSubtreeCycles groups (2*node+1) height
    else 37

theorem cap_cycles_le_old (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node height ≤ PackedOpening.capSubtreeCycles groups node height := by
  induction height generalizing node with
  | zero => rfl
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    simp only [capSubtreeCycles, PackedOpening.capSubtreeCycles]
    split <;> omega

private def capWorst : Nat → Nat
  | 0 => 56
  | height+1 => 14 + 2*capWorst height

private theorem cap_worst_lower (height : Nat) : 56 ≤ capWorst height := by
  induction height with
  | zero => decide
  | succ height ih => simp only [capWorst]; omega

private theorem cap_sharp_bound (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node (height+1) ≤ capWorst height := by
  induction height generalizing node with
  | zero =>
    rw [capSubtreeCycles, cap_marked_children]
    cases left : capIsMarked groups (2*node) 0 <;>
      cases right : capIsMarked groups (2*node+1) 0 <;>
      simp [capSubtreeCycles, capWorst, left, right]
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have lower := cap_worst_lower height
    rw [capSubtreeCycles, capWorst]
    split <;> omega

/-- A height-one marked subtree has at least one occupied child; recurse through the eight cap levels. -/
theorem cap_cycles_bound (groups : List Nat) : capSubtreeCycles groups 1 8 ≤ 8946 :=
  cap_sharp_bound groups 1 7

def capCopySaving (dest : Nat) : Nat := 28-CapCopy.cycles dest

/-- Prefix potential for the serialized cap nodes, including each eighth node's cursor fold. -/
def capCopySavings (base : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => capCopySavings base n+capCopySaving (base+capOffset n)

theorem cap_copy_cycles_bounds (dest : Nat) : 13 ≤ CapCopy.cycles dest ∧ CapCopy.cycles dest ≤ 26 := by
  unfold CapCopy.cycles
  split <;> (try split) <;> omega

theorem cap_copy_saving_bounds (dest : Nat) : 2 ≤ capCopySaving dest ∧ capCopySaving dest ≤ 15 := by
  have := cap_copy_cycles_bounds dest
  unfold capCopySaving
  omega

theorem cap_savings_segment (base start count : Nat) :
    capCopySavings base start+2*count ≤ capCopySavings base (start+count) ∧
    capCopySavings base (start+count) ≤ capCopySavings base start+15*count := by
  induction count with
  | zero => simp
  | succ count ih =>
    have := cap_copy_saving_bounds (base+capOffset (start+count))
    rw [show start+(count+1)=start+count+1 by omega, capCopySavings]
    omega

private theorem cap_saving_mod (dest : Nat) : capCopySaving dest=capCopySaving (dest%8) := by
  have four : dest%8%4=dest%4 := by omega
  simp only [capCopySaving, CapCopy.cycles, four, Nat.mod_mod]

private theorem cap_savings_eight (base k : Nat) (even : base%2=0) :
    ((List.range 8).map (fun j => capCopySaving (base+capOffset (8*k+j)))).sum=58 := by
  have periodic (j : Nat) (small : j<8) :
      capCopySaving (base+capOffset (8*k+j))=
        capCopySaving (base%8+capOffset (8*(k%4)+j)) := by
    rw [cap_saving_mod (base+capOffset (8*k+j)), cap_saving_mod (base%8+capOffset (8*(k%4)+j))]
    congr 1
    have offset (q : Nat) : capOffset (8*q+j)=238*q+30*j := by
      unfold capOffset
      have div : (8*q+j)/8=q := by omega
      rw [div]
      omega
    rw [offset k, offset (k%4)]
    omega
  have same : (List.range 8).map (fun j => capCopySaving (base+capOffset (8*k+j)))=
      (List.range 8).map (fun j => capCopySaving (base%8+capOffset (8*(k%4)+j))) := by
    apply List.map_congr_left
    intro j hj
    exact periodic j (List.mem_range.1 hj)
  rw [same]
  have table : ∀ b : Fin 8, ∀ q : Fin 4, b.val%2=0 →
      ((List.range 8).map (fun j => capCopySaving (b.val+capOffset (8*q.val+j)))).sum=58 := by
    decide +kernel
  exact table ⟨base%8, by omega⟩ ⟨k%4, by omega⟩ (by change base%8%2=0; omega)

private theorem cap_savings_add_eight (base n : Nat) :
    capCopySavings base (n+8)=capCopySavings base n+
      ((List.range 8).map (fun j => capCopySaving (base+capOffset (n+j)))).sum := by
  simp [capCopySavings, List.range_succ, Nat.add_assoc]

private theorem cap_savings_blocks (base k : Nat) (even : base%2=0) :
    capCopySavings base (8*k)=58*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, cap_savings_add_eight, cap_savings_eight base k even, ih]
    omega

theorem cap_savings_lower (base count : Nat) (even : base%2=0) :
    2*count+42*(count/8) ≤ capCopySavings base count := by
  have h := (cap_savings_segment base (8*(count/8)) (count%8)).1
  rw [show 8*(count/8)+count%8=count by omega, cap_savings_blocks base (count/8) even] at h
  omega

theorem cap_cycles_frontier_lower (groups : List Nat) (node height : Nat) :
    37*(capFrontierNodes groups node height).length ≤ capSubtreeCycles groups node height := by
  induction height generalizing node with
  | zero => simp only [capSubtreeCycles, capFrontierNodes]; split <;> simp
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    simp only [capSubtreeCycles, capFrontierNodes]
    split <;> simp only [List.length_append, List.length_singleton] <;> omega

private def capControlWorst : Nat → Nat
  | 0 => 5
  | h+1 => 14+2*capControlWorst h

private theorem cap_control_lower (height : Nat) : 5 ≤ capControlWorst height := by
  induction height with
  | zero => rfl
  | succ height ih => simp only [capControlWorst]; omega

theorem cap_cycles_control_bound (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node height ≤ capControlWorst height+32*(capFrontierNodes groups node height).length := by
  induction height generalizing node with
  | zero => simp only [capSubtreeCycles, capFrontierNodes, capControlWorst]; split <;> simp
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have low := cap_control_lower height
    simp only [capSubtreeCycles, capFrontierNodes, capControlWorst]
    split <;> simp only [List.length_append, List.length_singleton] <;> omega

/-- Exact subtree charge: reference traversal and folds, minus the telescoping copy potential. -/
def capWalkCycles (groups : List Nat) (node height base start : Nat) : Nat :=
  let count := (capFrontierNodes groups node height).length
  capSubtreeCycles groups node height+2*count+34*((start+count)/8-start/8)-
    (capCopySavings base (start+count)-capCopySavings base start)

theorem cap_walk_balance (groups : List Nat) (node height base start : Nat) :
    capWalkCycles groups node height base start+capCopySavings base (start+(capFrontierNodes groups node height).length)=
      capSubtreeCycles groups node height+2*(capFrontierNodes groups node height).length+
        34*((start+(capFrontierNodes groups node height).length)/8-start/8)+capCopySavings base start := by
  have := cap_cycles_frontier_lower groups node height
  have := cap_savings_segment base start (capFrontierNodes groups node height).length
  unfold capWalkCycles
  dsimp only
  omega

theorem cap_walk_le_old (groups : List Nat) (node height base : Nat) :
    capWalkCycles groups node height base 0 ≤ capSubtreeCycles groups node height+
      4*(capFrontierNodes groups node height).length+34*((capFrontierNodes groups node height).length/8) := by
  unfold capWalkCycles
  simp only [Nat.zero_add, Nat.zero_div, Nat.sub_zero]
  omega

theorem cap_walk_unmarked (groups : List Nat) (node height base start : Nat)
    (mark : capIsMarked groups node height=false) :
    capWalkCycles groups node height base start=CapCopy.cycles (base+capOffset start)+11+
      34*((start+1)/8-start/8) := by
  have count : (capFrontierNodes groups node height).length=1 := by
    cases height <;> simp [capFrontierNodes, mark]
  have old : capSubtreeCycles groups node height=37 := by
    cases height <;> simp [capSubtreeCycles, mark]
  have balance := cap_walk_balance groups node height base start
  rw [count, old, capCopySavings] at balance
  have := cap_copy_cycles_bounds (base+capOffset start)
  unfold capCopySaving at balance
  omega

theorem cap_walk_branch (groups : List Nat) (node height base start : Nat)
    (mark : capIsMarked groups node (height+1)=true) :
    capWalkCycles groups node (height+1) base start=
      14+capWalkCycles groups (2*node) height base start+
        capWalkCycles groups (2*node+1) height base (start+(capFrontierNodes groups (2*node) height).length) := by
  have parent := cap_walk_balance groups node (height+1) base start
  have left := cap_walk_balance groups (2*node) height base start
  have right := cap_walk_balance groups (2*node+1) height base
    (start+(capFrontierNodes groups (2*node) height).length)
  simp only [capSubtreeCycles, capFrontierNodes, mark, ite_true, List.length_append] at parent
  have m1 : start/8 ≤ (start+(capFrontierNodes groups (2*node) height).length)/8 := Nat.div_le_div_right (by omega)
  have m2 : (start+(capFrontierNodes groups (2*node) height).length)/8 ≤
      (start+(capFrontierNodes groups (2*node) height).length+(capFrontierNodes groups (2*node+1) height).length)/8 :=
    Nat.div_le_div_right (by omega)
  simp only [Nat.add_assoc] at parent left right m2
  omega

theorem cap_walk_scored_bound (groups : List Nat) (base : Nat) (even : base%2=0)
    (small : (capFrontierNodes groups 1 8).length ≤ 128) : capWalkCycles groups 1 8 base 0 ≤ 8818 := by
  have control := cap_cycles_control_bound groups 1 8
  have lower := cap_savings_lower base (capFrontierNodes groups 1 8).length even
  have balance := cap_walk_balance groups 1 8 base 0
  have exactControl : capControlWorst 8=4850 := by decide
  rw [exactControl] at control
  simp only [Nat.zero_add, Nat.zero_div, Nat.sub_zero, capCopySavings] at balance
  omega

/-! ### The chunked walk

DFS over heights 8..3 (levels 0..5); a marked level-5 node hands its depth-3 subtree to the chunk code, which
emits the frontier from the block of its leaf mask. -/

/-- Words of the block entry for relative frontier node `r`: `addi`, `srli` unless `r` is a leaf, `jal x18`. -/
def entryLen (r : Nat) : Nat := if depthOf r = 3 then 2 else 3

/-- Reference charge of one block entry: its words, the emit block (28 assumed for the copy, +7) and the return
`jalr`, less the 2 that `capWalkB` adds back per node. -/
def entryCycles (r : Nat) : Nat := entryLen r+34

/-- Reference charge of a marked level-5 subtree: the lookup (4), the level branch and the chunk jump (2), the
mask build and dispatch (28), the block exit (2) and one entry per frontier node. -/
def chunkControl (mask : Nat) : Nat := 36+((chunkEntries mask).map entryCycles).sum

/-- Reference charge of the chunked walk of a subtree of height `k+3`. A DFS emit costs 39: the lookup (4), the
stub (1), the emit block (28+7) and the return (1), less 2. A marked node above level 5 costs 14 as before. -/
def capSubtreeB (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 3 then chunkControl (leafMask groups node) else 39
  | k+1 =>
    if capIsMarked groups node (k+4) then
      14+capSubtreeB groups (2*node) k+capSubtreeB groups (2*node+1) k
    else 39

/-- Exact chunked walk charge: reference charge and folds, minus the telescoping copy potential. -/
def capWalkB (groups : List Nat) (node k base start : Nat) : Nat :=
  let count := (capFrontierNodes groups node (k+3)).length
  capSubtreeB groups node k+2*count+34*((start+count)/8-start/8)-
    (capCopySavings base (start+count)-capCopySavings base start)

theorem entry_cycles_lower (r : Nat) : 36 ≤ entryCycles r := by
  unfold entryCycles entryLen; split <;> omega

private theorem sum_lower (rs : List Nat) : 36*rs.length ≤ (rs.map entryCycles).sum := by
  induction rs with
  | nil => simp
  | cons r rest ih => have := entry_cycles_lower r; simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem chunk_count (groups : List Nat) (node : Nat) :
    (capFrontierNodes groups node 3).length=(chunkEntries (leafMask groups node)).length := by
  rw [chunk_frontier, List.length_map]

theorem cap_b_frontier_lower (groups : List Nat) (node k : Nat) :
    36*(capFrontierNodes groups node (k+3)).length ≤ capSubtreeB groups node k := by
  induction k generalizing node with
  | zero =>
    simp only [capSubtreeB, Nat.zero_add]
    split
    · rw [chunk_count]; have := sum_lower (chunkEntries (leafMask groups node)); unfold chunkControl; omega
    · rename_i h; simp [capFrontierNodes, h]
  | succ k ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    rw [show k+1+3=(k+3)+1 by omega, capFrontierNodes]
    simp only [capSubtreeB, show k+3+1=k+4 by omega]
    split <;> simp only [List.length_append, List.length_singleton] <;> omega

theorem cap_b_balance (groups : List Nat) (node k base start : Nat) :
    capWalkB groups node k base start+capCopySavings base (start+(capFrontierNodes groups node (k+3)).length)=
      capSubtreeB groups node k+2*(capFrontierNodes groups node (k+3)).length+
        34*((start+(capFrontierNodes groups node (k+3)).length)/8-start/8)+capCopySavings base start := by
  have := cap_b_frontier_lower groups node k
  have := cap_savings_segment base start (capFrontierNodes groups node (k+3)).length
  unfold capWalkB
  dsimp only
  omega

theorem cap_walk_b_unmarked (groups : List Nat) (node k base start : Nat)
    (mark : capIsMarked groups node (k+3)=false) :
    capWalkB groups node k base start=CapCopy.cycles (base+capOffset start)+13+34*((start+1)/8-start/8) := by
  have count : (capFrontierNodes groups node (k+3)).length=1 := by
    rw [show k+3=(k+2)+1 by omega]; simp [capFrontierNodes, show k+2+1=k+3 by omega, mark]
  have old : capSubtreeB groups node k=39 := by
    cases k with
    | zero =>
      have m : capIsMarked groups node 3=false := mark
      simp [capSubtreeB, m]
    | succ k =>
      have m : capIsMarked groups node (k+4)=false := mark
      simp [capSubtreeB, m]
  have balance := cap_b_balance groups node k base start
  rw [count, old, capCopySavings] at balance
  have := cap_copy_cycles_bounds (base+capOffset start)
  unfold capCopySaving at balance
  omega

theorem cap_walk_b_branch (groups : List Nat) (node k base start : Nat)
    (mark : capIsMarked groups node (k+4)=true) :
    capWalkB groups node (k+1) base start=
      14+capWalkB groups (2*node) k base start+
        capWalkB groups (2*node+1) k base (start+(capFrontierNodes groups (2*node) (k+3)).length) := by
  have parent := cap_b_balance groups node (k+1) base start
  have left := cap_b_balance groups (2*node) k base start
  have right := cap_b_balance groups (2*node+1) k base
    (start+(capFrontierNodes groups (2*node) (k+3)).length)
  have frontier : capFrontierNodes groups node (k+1+3)=
      capFrontierNodes groups (2*node) (k+3)++capFrontierNodes groups (2*node+1) (k+3) := by
    rw [show k+1+3=(k+3)+1 by omega]; simp [capFrontierNodes, show k+3+1=k+4 by omega, mark]
  rw [frontier] at parent
  simp only [capSubtreeB, mark, ite_true, List.length_append] at parent
  have m1 : start/8 ≤ (start+(capFrontierNodes groups (2*node) (k+3)).length)/8 := Nat.div_le_div_right (by omega)
  have m2 : (start+(capFrontierNodes groups (2*node) (k+3)).length)/8 ≤
      (start+(capFrontierNodes groups (2*node) (k+3)).length+(capFrontierNodes groups (2*node+1) (k+3)).length)/8 :=
    Nat.div_le_div_right (by omega)
  simp only [Nat.add_assoc] at parent left right m2
  omega

/-- Exact charge of the block entries for frontier nodes `rs`, the first written as cap node number `start`. -/
def entriesCycles : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | r :: rest, base, start =>
    entryLen r+8+CapCopy.cycles (base+capOffset start)+34*((start+1)/8-start/8)+entriesCycles rest base (start+1)

theorem entries_balance (base : Nat) : ∀ (rs : List Nat) (start : Nat),
    entriesCycles rs base start+capCopySavings base (start+rs.length)=
      (rs.map entryCycles).sum+2*rs.length+34*((start+rs.length)/8-start/8)+capCopySavings base start
  | [], start => by simp [entriesCycles]
  | r :: rest, start => by
    have ih := entries_balance base rest (start+1)
    have bounds := cap_copy_cycles_bounds (base+capOffset start)
    have step : capCopySavings base (start+1)=capCopySavings base start+capCopySaving (base+capOffset start) := rfl
    have m1 : start/8 ≤ (start+1)/8 := Nat.div_le_div_right (by omega)
    have m2 : (start+1)/8 ≤ (start+1+rest.length)/8 := Nat.div_le_div_right (by omega)
    simp only [entriesCycles, List.map_cons, List.sum_cons, List.length_cons, entryCycles]
    rw [show start+(rest.length+1)=start+1+rest.length by omega]
    unfold capCopySaving at step
    omega

theorem cap_walk_b_chunk (groups : List Nat) (node base start : Nat)
    (mark : capIsMarked groups node 3=true) :
    capWalkB groups node 0 base start=36+entriesCycles (chunkEntries (leafMask groups node)) base start := by
  have balance := cap_b_balance groups node 0 base start
  have entries := entries_balance base (chunkEntries (leafMask groups node)) start
  rw [chunk_count] at balance
  simp only [capSubtreeB, mark, ite_true, chunkControl] at balance
  omega

private def capControlB : Nat → Nat
  | 0 => 38
  | k+1 => 14+2*capControlB k

private theorem cap_control_b_lower (k : Nat) : 38 ≤ capControlB k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [capControlB]; omega

/-- Every block charges at most 38 plus 36 per frontier node (checked for all 256 masks). -/
theorem chunk_control_bound : ∀ mask < 256, chunkControl mask ≤ 38+36*(chunkEntries mask).length := by
  decide +kernel

theorem cap_b_control_bound (groups : List Nat) (node k : Nat) :
    capSubtreeB groups node k ≤ capControlB k+36*(capFrontierNodes groups node (k+3)).length := by
  induction k generalizing node with
  | zero =>
    simp only [capSubtreeB, capControlB, Nat.zero_add]
    split
    · rw [chunk_count]; exact chunk_control_bound _ (leaf_mask_lt groups node)
    · rename_i h; simp [capFrontierNodes, h]
  | succ k ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have low := cap_control_b_lower k
    rw [show k+1+3=(k+3)+1 by omega, capFrontierNodes]
    simp only [capSubtreeB, capControlB, show k+3+1=k+4 by omega]
    split <;> simp only [List.length_append, List.length_singleton] <;> omega

theorem cap_walk_b_scored_bound (groups : List Nat) (base : Nat) (even : base%2=0)
    (small : (capFrontierNodes groups 1 8).length ≤ 128) : capWalkB groups 1 5 base 0 ≤ 6130 := by
  have control := cap_b_control_bound groups 1 5
  have lower := cap_savings_lower base (capFrontierNodes groups 1 8).length even
  have balance := cap_b_balance groups 1 5 base 0
  have exactControl : capControlB 5=1650 := by decide
  rw [exactControl] at control
  simp only [show (5:Nat)+3=8 from rfl] at control balance
  simp only [Nat.zero_add, Nat.zero_div, Nat.sub_zero, capCopySavings] at balance
  omega

theorem cap_frontier_length_le (groups : List Nat) (node h : Nat) :
    (capFrontierNodes groups node h).length ≤ 2^h := by
  induction h generalizing node with
  | zero => simp only [capFrontierNodes]; split <;> simp
  | succ h ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have one := Nat.one_le_two_pow (n := h)
    rw [capFrontierNodes]
    split <;> simp only [List.length_append, List.length_singleton, pow_succ] <;> omega

/-- A crude bound for every position set (the fuel allowance). -/
theorem cap_walk_b_bound (groups : List Nat) (base : Nat) (even : base%2=0) : capWalkB groups 1 5 base 0 ≤ 12498 := by
  have control := cap_b_control_bound groups 1 5
  have lower := cap_savings_lower base (capFrontierNodes groups 1 8).length even
  have balance := cap_b_balance groups 1 5 base 0
  have count := cap_frontier_length_le groups 1 8
  have exactControl : capControlB 5=1650 := by decide
  rw [exactControl] at control
  simp only [show (5:Nat)+3=8 from rfl] at control balance
  simp only [Nat.zero_add, Nat.zero_div, Nat.sub_zero, capCopySavings] at balance
  norm_num at count
  omega

end TwoPermutationPrototype.GroupedOpening
