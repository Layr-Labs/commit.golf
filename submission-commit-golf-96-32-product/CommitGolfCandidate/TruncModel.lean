import CommitGolfCandidate.Binding
import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.TruncBirthday

namespace CommitGolfCandidate.Trunc
open CommitGolf

def masked (node : Nat) : Prop := 2 ≤ node ∧ node < 2^22
instance (node : Nat) : Decidable (masked node) := inferInstanceAs (Decidable (2≤node ∧ node<2^22))

def padLow (x : Digest) : Digest := (0 : BitVec 16) ++ low240 x

def storeNode (node : Nat) (x : Digest) : Digest :=
  if masked node then padLow x else x

@[simp] theorem low_store (node : Nat) (x : Digest) : low240 (storeNode node x)=low240 x := by
  unfold storeNode
  split
  · exact BitVec.extractLsb'_append_eq_right (a:=(0 : BitVec 16)) (b:=low240 x)
  · rfl

def parent (H : Compression) (n : Nat) (l r : Digest) := storeNode n (combine H l r)

def pathInput (v : Digest) (item : Bool × Digest) : BitVec COMPRESSION_INPUT_LENGTH :=
  if item.1 then padInput (v ++ item.2) else padInput (item.2 ++ v)

def climb (H : Compression) (node : Nat) (v : Digest) : List (Bool × Digest) → Digest
  | [] => v
  | item::rest => climb H (node/2) (storeNode (node/2) (H (pathInput v item))) rest

def pathInputs (H : Compression) (node : Nat) (v : Digest) :
    List (Bool × Digest) → List (BitVec COMPRESSION_INPUT_LENGTH)
  | [] => []
  | item::rest => let x := pathInput v item
                  x :: pathInputs H (node/2) (storeNode (node/2) (H x)) rest

theorem pathInputs_length (H : Compression) (n : Nat) (v : Digest) (p : List (Bool × Digest)) :
    (pathInputs H n v p).length=p.length := by induction p generalizing n v <;> simp [pathInputs, *]

theorem climb_append (H : Compression) (n : Nat) (v : Digest) (a b : List (Bool × Digest)) :
    climb H n v (a++b) = climb H (n/2^a.length) (climb H n v a) b := by
  induction a generalizing n v with
  | nil => simp [climb]
  | cons h t ih =>
    simp only [List.cons_append,climb,List.length_cons,ih,Nat.div_div_eq_div_mul]
    rw [Nat.pow_succ, Nat.mul_comm (2^t.length) 2]

def referenceHeap (H : Compression) (N : Nat) (leaf : Nat → Digest) (n : Nat) : Digest :=
  if h : 0<n ∧ n<N then parent H n (referenceHeap H N leaf (2*n)) (referenceHeap H N leaf (2*n+1))
  else if N≤n ∧ n<2*N then leaf (n-N) else 0
termination_by 2*N-n
decreasing_by all_goals omega

theorem reference_heap_parent (H : Compression) (N : Nat) (leaf : Nat→Digest) (n : Nat) (hp : 0<n) (hb : n<N) :
    referenceHeap H N leaf n = parent H n (referenceHeap H N leaf (2*n)) (referenceHeap H N leaf (2*n+1)) := by
  rw [referenceHeap,dif_pos ⟨hp,hb⟩]

theorem reference_heap_leaf (H : Compression) (N : Nat) (leaf : Nat→Digest) (i : Nat) (hi : i<N) :
    referenceHeap H N leaf (N+i)=leaf i := by
  rw [referenceHeap,dif_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]

theorem heap_eq_reference (H : Compression) (N : Nat) (leaf heap : Nat→Digest)
    (parents : ∀ n,0<n → n<N → heap n=parent H n (heap (2*n)) (heap (2*n+1)))
    (leaves : ∀ i,i<N → heap (N+i)=leaf i) (n : Nat) (pos : 0<n) (small : n<2*N) :
    heap n=referenceHeap H N leaf n := by
  by_cases branch : n<N
  · rw [parents n pos branch,reference_heap_parent H N leaf n pos branch]
    exact congrArg₂ (parent H n) (heap_eq_reference H N leaf heap parents leaves (2*n) (by omega) (by omega))
      (heap_eq_reference H N leaf heap parents leaves (2*n+1) (by omega) (by omega))
  · have a : N+(n-N)=n := by omega
    exact a ▸ (leaves (n-N) (by omega)).trans (reference_heap_leaf H N leaf (n-N) (by omega)).symm
termination_by 2*N-n
decreasing_by all_goals omega

end CommitGolfCandidate.Trunc
