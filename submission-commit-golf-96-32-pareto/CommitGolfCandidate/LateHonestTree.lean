import CommitGolfCandidate.LateOpenPathModel
import CommitGolfCandidate.LateCheckModel
import CommitGolfCandidate.LateCachedTree

namespace CommitGolfCandidate.Late.Check
open CommitGolf

structure HonestTree (h : Compression) (m : Message) (s : SaltTape) (t : Levels) : Prop where
  start : ∀ i : Index, node t 0 i.val = leaf h (i.val.testBit 0) (s i) (m i)
  pair : ∀ d j, d<LOG_LENGTH → j<levelCount (d+1) →
    node t (d+1) j = combine h (node t d (2*j)) (node t d (2*j+1))

private theorem finAt {α : Type} (n : Nat) (f : Fin n → α) (j : Fin n) (v : α) :
    ((List.finRange n).map f)[j.val]?.getD v = f j := by
  have hi : j.val < (List.finRange n).length := by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

attribute [local irreducible] List.finRange treeM node

theorem honestTree (h : Compression) (m : Message) (s : SaltTape) :
    HonestTree h m s (treeM (M:=Id) h m s) := by
  constructor
  · intro i
    rw [fixed_tree_node _ _ _ 0 i.val (by decide) i.isLt]
    exact finAt LENGTH (fun i => leaf h (i.val.testBit 0) (s i) (m i)) i 0
  · intro d j hd hj
    have width := level_successor d hd
    rw [fixed_tree_node _ _ _ (d+1) j (by omega) hj,
      fixed_tree_node _ _ _ d (2*j) (by omega) (by omega),
      fixed_tree_node _ _ _ d (2*j+1) (by omega) (by omega)]
    exact parent_compatible .. 

theorem HonestTree.climb (h : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree h m s t) (i : Index) (d : Nat) (hd : d≤LOG_LENGTH) :
    CommitGolfCandidate.climb h (leaf h (i.val.testBit 0) (s i) (m i))
      (path i d (fun l => node t l (Open.mate i l))) = node t d (Open.indexAbove i d) := by
  induction d with
  | zero => simpa [path,CommitGolfCandidate.climb,Open.indexAbove] using (tree.start i).symm
  | succ d ih =>
    have prior := ih (by omega)
    let k := Open.indexAbove i d
    let q := Open.indexAbove i (d+1)
    have div : q=k/2 := Open.above_next i d
    have par := tree.pair d q (by omega) (Open.above_bound i (d+1) hd)
    unfold path CommitGolfCandidate.climb at *
    rw [List.range_succ,List.map_append,List.foldl_append]
    simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,prior]
    change (if i.val.testBit d then combine h (node t d (k ^^^ 1)) (node t d k)
      else combine h (node t d k) (node t d (k ^^^ 1))) = node t (d+1) q
    rw [Nat.testBit_eq_decide_div_mod_eq]
    change (if decide (k%2=1) then _ else _) = _
    by_cases odd : k%2=1
    · rw [if_pos (by simp [odd]),Nat.xor_one_of_odd (Nat.odd_iff.mpr odd),par]
      congr 2 <;> omega
    · rw [if_neg (by simp [odd]),Nat.xor_one_of_even (Nat.even_iff.mpr (by omega)),par]
      congr 2 <;> omega

theorem HonestTree.upper (h : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree h m s t) (tab : Nat → Digest) (cap : ∀ j<128, tab j=node t 17 j) :
    referenceHeap h 128 tab 1 = node t LOG_LENGTH 0 := by
  have layer (d : Nat) (height : d≤7) (j : Nat) (hj : j<2^(7-d)) :
      referenceHeap h 128 tab (2^(7-d)+j) = node t (17+d) j := by
    induction d generalizing j with
    | zero => exact (reference_heap_leaf h 128 tab j hj).trans (cap j hj)
    | succ d ih =>
      have eq : 7-d=(7-(d+1))+1 := by omega
      have dbl : 2^(7-d)=2^(7-(d+1))*2 := by rw [eq,Nat.pow_succ]
      have bound : 2^(7-d)≤128 := Nat.pow_le_pow_right (by decide) (Nat.sub_le 7 d)
      have pos : 0<2^(7-(d+1)) := by positivity
      have hWidth : levelCount (17+d+1)=2^(7-(d+1)) := by
        unfold levelCount;congr 1;change 24-(17+d+1)=_;omega
      rw [reference_heap_parent h 128 tab _ (by omega) (by omega),
        show 2*(2^(7-(d+1))+j)=2^(7-d)+(2*j) by omega,
        show 2^(7-d)+2*j+1=2^(7-d)+(2*j+1) by omega,
        ih (by omega) (2*j) (by omega),ih (by omega) (2*j+1) (by omega)]
      exact (tree.pair (17+d) j (by change 17+d<24;omega) (by rw [hWidth];exact hj)).symm
  exact layer 7 (by decide) 0 (by decide)

end CommitGolfCandidate.Late.Check
