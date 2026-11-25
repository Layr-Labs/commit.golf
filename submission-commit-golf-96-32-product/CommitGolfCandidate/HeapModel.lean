import CommitGolfCandidate.Model
import Mathlib.Data.Nat.Bitwise

/-! Authentication paths for the heap layout used by the submitted machine.
The root is slot 1; children of slot p are slots 2*p and 2*p+1. -/
namespace CommitGolfCandidate
open CommitGolf

/-- The opening image repeatedly copies the sibling at `node xor 1`, then divides
its heap index by two. Each Boolean says whether this node is a right child. -/
def heapPath (heap : Nat → Digest) (node : Nat) : Nat → List (Bool × Digest)
  | 0 => []
  | count+1 => (node.testBit 0, heap (node ^^^ 1)) :: heapPath heap (node/2) count

theorem heap_path_length (heap : Nat → Digest) (node count : Nat) :
    (heapPath heap node count).length = count := by
  induction count generalizing node with
  | zero => rfl
  | succ count ih => simp only [heapPath, List.length_cons, ih]

private theorem heap_parent_step (compress : Compression) (heap : Nat → Digest) (node : Nat)
    (parent : heap (node/2) = combine compress (heap (2*(node/2))) (heap (2*(node/2)+1))) :
    (if node.testBit 0 then combine compress (heap (node ^^^ 1)) (heap node)
      else combine compress (heap node) (heap (node ^^^ 1))) = heap (node/2) := by
  by_cases even : node%2 = 0
  · have sibling := Nat.xor_one_of_even (Nat.even_iff.mpr even)
    have left : 2*(node/2) = node := by omega
    simpa only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one,
      even, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false, sibling, left] using parent.symm
  · have odd : node%2 = 1 := by omega
    have sibling := Nat.xor_one_of_odd (Nat.odd_iff.mpr odd)
    have left : 2*(node/2) = node-1 := by omega
    have right : 2*(node/2)+1 = node := by omega
    simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one,
      odd, decide_true, ite_true, sibling]
    exact (congrArg₂ (combine compress) (congrArg heap left.symm)
      (congrArg heap right.symm)).trans parent.symm

/-- If each stored parent is the compression of its two children, the actual heap
copath reconstructs the ancestor at the requested height. -/
theorem reconstruct_heap_ancestor (compress : Compression) (heap : Nat → Digest)
    (leaves : Nat)
    (parents : ∀ parent, 0 < parent → parent < leaves →
      heap parent = combine compress (heap (2*parent)) (heap (2*parent+1)))
    (count node : Nat) (below : node < 2*leaves) (height : 2^count ≤ node) :
    climb compress (heap node) (heapPath heap node count) = heap (node / 2^count) := by
  induction count generalizing node with
  | zero => simp [heapPath, climb]
  | succ count ih =>
    have positive : 0 < 2^count := by positivity
    have power : 2^(count+1) = 2*2^count := by rw [Nat.pow_succ]; omega
    have current : 2 ≤ node := by rw [power] at height; omega
    have parentPositive : 0 < node/2 := by omega
    have parentBound : node/2 < leaves := by omega
    have parentHeight : 2^count ≤ node/2 := by rw [power] at height; omega
    have step := heap_parent_step compress heap node (parents (node/2) parentPositive parentBound)
    change climb compress
      (if node.testBit 0 then combine compress (heap (node ^^^ 1)) (heap node)
        else combine compress (heap node) (heap (node ^^^ 1))) (heapPath heap (node/2) count) = _
    rw [step, ih (node/2) (by omega) parentHeight, Nat.div_div_eq_div_mul, ← power]

/-- Only the parents strictly above slot `low` need be consistent when the climb stops
at an ancestor above `low` (here: at a cap node). -/
theorem reconstruct_heap_ancestor_above (compress : Compression) (heap : Nat → Digest)
    (low leaves : Nat)
    (parents : ∀ parent, low < parent → parent < leaves →
      heap parent = combine compress (heap (2*parent)) (heap (2*parent+1)))
    (count node : Nat) (below : node < 2*leaves) (height : (low+1) * 2^count ≤ node) :
    climb compress (heap node) (heapPath heap node count) = heap (node / 2^count) := by
  induction count generalizing node with
  | zero => simp [heapPath, climb]
  | succ count ih =>
    have positive : 0 < 2^count := by positivity
    have power : (low+1) * 2^(count+1) = 2*((low+1) * 2^count) := by rw [Nat.pow_succ]; ring
    have least : low + 1 ≤ (low+1) * 2^count := Nat.le_mul_of_pos_right _ positive
    rw [power] at height
    have parentBound : node/2 < leaves := by omega
    have parentAbove : low < node/2 := by omega
    have parentHeight : (low+1) * 2^count ≤ node/2 := by omega
    have step := heap_parent_step compress heap node (parents (node/2) parentAbove parentBound)
    change climb compress
      (if node.testBit 0 then combine compress (heap (node ^^^ 1)) (heap node)
        else combine compress (heap node) (heap (node ^^^ 1))) (heapPath heap (node/2) count) = _
    rw [step, ih (node/2) (by omega) parentHeight, Nat.div_div_eq_div_mul,
      show 2 * 2^count = 2^(count+1) by rw [Nat.pow_succ]; omega]

/-- A path from any leaf of the complete heap reaches the root at slot 1. -/
theorem reconstruct_heap_root (compress : Compression) (heap : Nat → Digest) (depth index : Nat)
    (inside : index < 2^depth)
    (parents : ∀ parent, 0 < parent → parent < 2^depth →
      heap parent = combine compress (heap (2*parent)) (heap (2*parent+1))) :
    climb compress (heap (2^depth+index)) (heapPath heap (2^depth+index) depth) = heap 1 := by
  rw [reconstruct_heap_ancestor compress heap (2^depth) parents depth (2^depth+index)
    (by omega) (by omega)]
  have positive : 0 < 2^depth := by positivity
  rw [Nat.add_div_left _ positive, Nat.div_eq_of_lt inside]

/-- The heap's leading level bit does not affect any of the leaf's path directions. -/
theorem heap_leaf_direction (depth index level : Nat) (inside : index < 2^depth)
    (below : level < depth) :
    (2^depth+index).testBit level = index.testBit level := by
  have reduced : (2^depth+index) % 2^depth = index := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt inside]
  have bits := congrArg (fun value : Nat => value.testBit level) reduced
  simpa only [Nat.testBit_mod_two_pow, below, decide_true, Bool.true_and] using bits

/-- Each serialized sibling and direction corresponds to the same heap level. -/
theorem heap_path_get (heap : Nat → Digest) (node count level : Nat) (inside : level < count) :
    (heapPath heap node count)[level]'(by rw [heap_path_length]; exact inside) =
      (node.testBit level, heap ((node/2^level) ^^^ 1)) := by
  induction count generalizing node level with
  | zero => omega
  | succ count ih =>
    cases level with
    | zero => simp only [heapPath, List.getElem_cons_zero, Nat.pow_zero, Nat.div_one]
    | succ level =>
      simp only [heapPath, List.getElem_cons_succ]
      rw [ih (node/2) level (by omega), Nat.testBit_div_two, Nat.div_div_eq_div_mul]
      simp only [Nat.pow_succ, Nat.mul_comm]

end CommitGolfCandidate
