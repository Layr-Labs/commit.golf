import CommitGolfCandidate.S5HidingTree
import CommitGolfCandidate.S5TreeNode
namespace CommitGolfCandidate.S5Machine
open CommitGolf
open CommitGolfCandidate.Late (Digest SaltTape node)

def initialList (H : Compression) (m : Message) (s : SaltTape) := LateHiding.leafLayer H m s
attribute [local irreducible] List.finRange treeNode

private theorem mapFinLen (n : Nat) (f : Fin n→Digest) : ((List.finRange n).map f).length=n := by rw [List.length_map,List.length_finRange]

private theorem parentLookup (H : Compression) (base : Nat→Digest) (h : Nat) (bh : h<24) (xs : List Digest)
    (all : ∀ i,xs[i]?.getD 0=treeNode H base h i) (j : Nat) :
    (S5Hiding.parents H h xs)[j]?.getD 0=treeNode H base (h+1) j := by
  have width : levelCount (h+1)=S4.width (h+1) := by unfold levelCount;rw [Nat.min_eq_left (by omega)]
  by_cases valid : j<levelCount (h+1)
  · have fits : j<(List.range (S4.width (h+1))).length:=by rw [List.length_range,←width];exact valid
    rw [treeNode]; erw [if_pos valid]
    simp only [S5Hiding.parents,List.getElem?_map,List.getElem?_eq_getElem fits,List.getElem_range,Option.map_some,Option.getD_some,
      parent_eval,all]
  · rw [missing_node _ _ _ _ (by omega)]
    have endOf : (List.range (S4.width (h+1))).length≤j:=by rw [List.length_range,←width];omega
    simp only [S5Hiding.parents,List.getElem?_map,List.getElem?_eq_none endOf,Option.map_none,Option.getD_none]

private theorem cacheReads (H : Compression) (base : Nat→Digest) (fuel h : Nat) (total : h+fuel=24)
    (xs : List Digest) (frame : ∀ i,xs[i]?.getD 0=treeNode H base h i) (n j : Nat) (bound : n≤fuel) :
    node (S5Hiding.levels H fuel xs) n j=treeNode H base (h+n) j := by
  induction fuel generalizing h xs n with
  | zero=>have z : n=0:=by omega
          subst n;exact frame j
  | succ d ih=>
    cases n with
    | zero=>exact frame j
    | succ n=>
      have hh : 23-d=h := by omega
      have sub:=ih (h+1) (by omega) (S5Hiding.parents H h xs) (parentLookup H base h (by omega) xs frame) n (by omega)
      change node (S5Hiding.levels H d (S5Hiding.parents H (23-d) xs)) n j=_
      rw [hh,show h+(n+1)=(h+1)+n by omega];exact sub

theorem fixed_tree_node_all (H : Compression) (m : Message) (s : SaltTape) (n j : Nat) (bn : n≤LOG_LENGTH) :
    node (S5Hiding.tree H m s) n j=treeNode H (fun k=>(initialList H m s)[k]?.getD 0) n j := by
  let xs:=initialList H m s
  have len : xs.length=LENGTH:=by unfold xs initialList LateHiding.leafLayer;rw [List.length_map,List.length_finRange]
  suffices frame : ∀ i,xs[i]?.getD 0=treeNode H (fun k=>xs[k]?.getD 0) 0 i by
    simpa only [xs,initialList,S5Hiding.tree,Nat.zero_add] using cacheReads H _ 24 0 (by decide) xs frame n j bn
  intro i
  rw [treeNode]
  by_cases hi : i<levelCount 0
  · rw [if_pos hi]
  · rw [if_neg hi,List.getElem?_eq_none (by rw [len];change ¬i<LENGTH at hi;omega)];rfl
theorem fixed_tree_node (H : Compression) (m : Message) (s : SaltTape) (n j : Nat) (bn : n≤LOG_LENGTH) (_ : j<levelCount n) :
    node (S5Hiding.tree H m s) n j=treeNode H (fun k=>(initialList H m s)[k]?.getD 0) n j :=
  fixed_tree_node_all H m s n j bn
end CommitGolfCandidate.S5Machine
