import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule
import CommitGolfCandidate.K3OpenCapBytes

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
  capSubtreeCycles groups node height+4*count+34*((start+count)/8-start/8)-
    (capCopySavings base (start+count)-capCopySavings base start)

theorem cap_walk_balance (groups : List Nat) (node height base start : Nat) :
    capWalkCycles groups node height base start+capCopySavings base (start+(capFrontierNodes groups node height).length)=
      capSubtreeCycles groups node height+4*(capFrontierNodes groups node height).length+
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
    capWalkCycles groups node height base start=CapCopy.cycles (base+capOffset start)+13+
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
    (small : (capFrontierNodes groups 1 8).length ≤ 128) : capWalkCycles groups 1 8 base 0 ≤ 9074 := by
  have control := cap_cycles_control_bound groups 1 8
  have lower := cap_savings_lower base (capFrontierNodes groups 1 8).length even
  have balance := cap_walk_balance groups 1 8 base 0
  have exactControl : capControlWorst 8=4850 := by decide
  rw [exactControl] at control
  simp only [Nat.zero_add, Nat.zero_div, Nat.sub_zero, capCopySavings] at balance
  omega

end TwoPermutationPrototype.GroupedOpening
