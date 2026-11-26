import CommitGolfCandidate.TruncModel
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 10000

theorem stored_parent_step (H : Compression) (heap : Nat→Digest) (node : Nat)
    (ok : heap (node/2)=parent H (node/2) (heap (2*(node/2))) (heap (2*(node/2)+1))) :
    storeNode (node/2) (H (pathInput (heap node) (node.testBit 0,heap (node ^^^ 1)))) = heap (node/2) := by
  rw [ok]
  unfold parent combine pathInput
  apply congrArg (storeNode (node/2));apply congrArg H
  by_cases even : node%2=0
  · have side := Nat.xor_one_of_even (Nat.even_iff.mpr even)
    have left : 2*(node/2)=node := by omega
    simp [Nat.testBit_eq_decide_div_mod_eq,even,side,left]
  · have odd : node%2=1 := by omega
    have side := Nat.xor_one_of_odd (Nat.odd_iff.mpr odd)
    have left : 2*(node/2)=node-1 := by omega
    have right : 2*(node/2)+1=node := by omega
    simp only [Nat.testBit_eq_decide_div_mod_eq,Nat.pow_zero,Nat.div_one,odd,decide_true,ite_true,side,right,left,show node-1+1=node by omega]

theorem reconstruct_heap_ancestor (H : Compression) (heap : Nat→Digest) (N : Nat)
    (parents : ∀ n,0<n → n<N → heap n=parent H n (heap (2*n)) (heap (2*n+1)))
    (count node : Nat) (below : node<2*N) (height : 2^count≤node) :
    climb H node (heap node) (heapPath heap node count)=heap (node/2^count) := by
  induction count generalizing node with
  | zero => simp [heapPath,climb]
  | succ k ih =>
    have power : 2^(k+1)=2*2^k := by rw [Nat.pow_succ,Nat.mul_comm]
    have positive : 0<2^k := by positivity
    have parentPos : 0<node/2 := by rw [power] at height;omega
    have h := stored_parent_step H heap node (parents _ parentPos (by omega))
    simp only [heapPath,climb,h]
    rw [ih (node/2) (by omega) (by rw [power] at height;omega),Nat.div_div_eq_div_mul,power]

theorem reconstruct_heap_root (H : Compression) (heap : Nat→Digest) (d index : Nat)
    (inside : index<2^d) (parents : ∀ n,0<n → n<2^d → heap n=parent H n (heap (2*n)) (heap (2*n+1))) :
    climb H (2^d+index) (heap (2^d+index)) (heapPath heap (2^d+index) d)=heap 1 := by
  rw [reconstruct_heap_ancestor H heap (2^d) parents d (2^d+index) (by omega) (by omega)]
  rw [Nat.add_div_left _ (by positivity),Nat.div_eq_of_lt inside]

end CommitGolfCandidate.Trunc
