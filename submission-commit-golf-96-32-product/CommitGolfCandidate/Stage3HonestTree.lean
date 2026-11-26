import CommitGolfCandidate.LateCachedTree
import CommitGolfCandidate.LateOpenPathModel
import CommitGolfCandidate.TruncHeap
import CommitGolfCandidate.LateReplay
namespace CommitGolfCandidate.Late
open CommitGolf

def heap (H : Compression) (m : Message) (s : SaltTape) :=
  Trunc.referenceHeap H LENGTH fun k=>(initialList H m s)[k]?.getD 0

private theorem levelMask (d j : Nat) (hd : d<LOG_LENGTH) (hj : j<levelCount (d+1)) :
    Trunc.masked (levelCount (d+1)+j) ↔ 0<23-d ∧ 23-d≤21 := by
  change d<24 at hd
  interval_cases d <;> simp only [levelCount,LOG_LENGTH,Trunc.masked] at hj ⊢ <;> norm_num at hj ⊢ <;> omega

theorem storedLayer (H : Compression) (d j : Nat) (x : Digest) (hd : d<LOG_LENGTH) (hj : j<levelCount (d+1)) :
    retain (23-d) x=Trunc.storeNode (levelCount (d+1)+j) x := by
  unfold retain Trunc.storeNode
  have eqn:=levelMask d j hd hj
  by_cases k : 0<23-d ∧ 23-d≤21
  · rw [if_pos k,if_pos (eqn.mpr k)];rfl
  · rw [if_neg k,if_neg (fun h=>k (eqn.mp h))]

theorem heapLevel (H : Compression) (m : Message) (s : SaltTape) (d j : Nat) (hd : d≤LOG_LENGTH) (hj : j<levelCount d) :
    node (treeM (M:=Id) H m s) d j = heap H m s (levelCount d+j) := by
  rw [fixed_tree_node H m s d j hd hj]
  induction d generalizing j with
  | zero => exact (Trunc.reference_heap_leaf H LENGTH _ j hj).symm
  | succ d ih =>
    have double:=level_successor d (by omega)
    have pos : 0<levelCount (d+1) := Nat.two_pow_pos _
    have small : levelCount d≤LENGTH := level_count_le d
    change layerHash H d (parentBlock _ _) = _
    rw [ih (2*j) (by omega) (by omega),ih (2*j+1) (by omega) (by omega)]
    unfold layerHash
    apply (storedLayer H d j _ (by omega) hj).trans
    apply (congrArg (Trunc.storeNode (levelCount (d+1)+j)) (parent_compatible H
      (heap H m s (levelCount d+2*j)) (heap H m s (levelCount d+(2*j+1))))).trans
    unfold heap
    rw [Trunc.reference_heap_parent H LENGTH _ (levelCount (d+1)+j) (by omega) (by omega)]
    unfold Trunc.parent
    rw [show levelCount d+2*j=2*(levelCount (d+1)+j) by omega,
      show levelCount d+(2*j+1)=2*(levelCount (d+1)+j)+1 by omega]

theorem aboveHeap (i : Index) (l : Nat) (hl : l≤LOG_LENGTH) :
    (LENGTH+i.val)/2^l=levelCount l+Open.indexAbove i l := by
  have power : levelCount l*2^l=LENGTH := by unfold levelCount LENGTH;rw [←Nat.pow_add,Nat.sub_add_cancel hl]
  have formula (a b k c : Nat) (eqn : c*k=a) (pos : 0<k) : (a+b)/k=c+b/k := by
    rw [←eqn,Nat.mul_comm c k,Nat.mul_add_div pos]
  exact formula LENGTH i.val _ _ power (by positivity)

theorem siblingHeap (i : Index) (l : Nat) (hl : l<LOG_LENGTH) :
    (((LENGTH+i.val)/2^l) ^^^ 1)=levelCount l+Open.mate i l := by
  let k:=Open.indexAbove i l
  rw [aboveHeap _ _ (by omega)];change (levelCount l+k ^^^ 1)=levelCount l+(k ^^^ 1)
  have double:=level_successor l hl
  by_cases e : k%2=0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr (by omega)),Nat.xor_one_of_even (Nat.even_iff.mpr e)];omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega)),Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))];omega

theorem layerIsPadded (H : Compression) (m : Message) (s : SaltTape) (l j : Nat) (lo : 3≤l) (hi : l<24) (inside : j<levelCount l) :
    ∃ v, node (treeM (M:=Id) H m s) l j=Trunc.padLow v := by
  cases l with
  | zero=>omega
  | succ d=>
    rw [fixed_tree_node H m s (d+1) j (by change d+1≤24;omega) inside]
    have formula (x : Digest) : ∃ v,retain (23-d) x=Trunc.padLow v := by
      refine ⟨x,?_⟩;unfold retain;rw [if_pos (by omega : 0<23-d ∧ 23-d≤21)];rfl
    exact formula _
end CommitGolfCandidate.Late
