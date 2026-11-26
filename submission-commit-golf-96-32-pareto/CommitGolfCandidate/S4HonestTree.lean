import CommitGolfCandidate.S4Auth
import CommitGolfCandidate.LateCachedTree

namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Digest SaltTape Levels node)

structure HonestTree (p : Profile) (H : Compression) (m : Message) (s : SaltTape) (t : Levels) : Prop where
  leaf : ∀ i : Index,node t 0 i.val=Late.leaf H (i.val.testBit 0) (s i) (m i)
  parent : ∀ h<24,∀ j < width (h+1),node t (h+1) j=retained p (h+1) (H (row h
    (node t h (radix h*j)) (node t h (radix h*j+1)) (node t h (radix h*j+2))))
  missing : ∀ h≤24,∀ j,width h≤j → node t h j=0

attribute [local irreducible] List.finRange Late.treeNode

private theorem finLookup {α : Type} (n : Nat) (f : Fin n→α) (i : Fin n) (z : α) :
    ((List.finRange n).map f)[i.val]?.getD z=f i := by
  have b : i.val<(List.finRange n).length:=by rw [List.length_finRange];exact i.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem b,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

private theorem initialLeaf (H : Compression) (m : Message) (s : SaltTape) (i : Index) :
    (Late.initialList H m s)[i.val]?.getD 0=Late.leaf H (i.val.testBit 0) (s i) (m i) := by
  unfold Late.initialList LateHiding.leafLayer
  exact (finLookup LENGTH (fun j=>LateHiding.leafDigest H (j.val.testBit 0) (s j) (m j)) i 0).trans
    (LateHiding.leaf_digest_eq ..)

theorem honestTree (H : Compression) (m : Message) (s : SaltTape) : HonestTree active H m s (S4Hiding.tree H m s) := by
  let base : Nat→Digest:=fun k=>(Late.initialList H m s)[k]?.getD 0
  have eqn (h j : Nat) (limit : h≤24) : node (S4Hiding.tree H m s) h j=Late.treeNode H base h j :=
    Late.fixed_tree_node_all _ _ _ _ _ limit
  have count (h : Nat) (b : h≤24) : Late.levelCount h=width h:=by unfold Late.levelCount;rw [Nat.min_eq_left b]
  constructor
  · intro i
    rw [eqn 0 i.val (by decide),Late.treeNode]
    exact (if_pos i.isLt).trans (initialLeaf H m s i)
  · intro h bh j bj
    simp only [eqn h _ (by omega),eqn (h+1) _ (by omega)]
    rw [Late.treeNode]
    exact if_pos (by rwa [count _ (by omega)] : j<Late.levelCount (h+1))
  · intro h bh j out
    rw [eqn h j bh];exact Late.missing_node _ _ _ _ ((count h bh).symm ▸ out)

def truePeers (t : Levels) (i : Index) (h : Nat) : Peers :=
  (sibling t i.val h 0,if h=0 then sibling t i.val h 1 else 0)

private theorem rotated (h j : Nat) (table : Nat→Digest) :
    let radix:=radix h
    let first:=radix*(j/radix)
    payload (lane h j) (table j) (table (first+(j%radix+1)%radix),
      if h=0 then table (first+(j%radix+2)%radix) else 0)=
      row h (table first) (table (first+1)) (table (first+2)) := by
  by_cases z : h=0
  · subst h
    have cases3 : j%3=0 ∨ j%3=1 ∨ j%3=2:=by omega
    rcases cases3 with k|k|k
    · have v : table j=table (3*(j/3)+0):=congrArg table (by omega)
      simp only [radix,lane,row,ite_true,k,payload,↓reduceIte, Nat.reduceMod,Nat.reduceAdd,Nat.add_zero]
      simp only [v,Nat.add_zero] <;> rfl
    · have v : table j=table (3*(j/3)+1):=congrArg table (by omega)
      simp only [radix,lane,row,ite_true,k,payload,↓reduceIte, Nat.reduceMod,Nat.reduceAdd,Nat.add_zero]
      simp only [v,Nat.add_zero] <;> rfl
    · have v : table j=table (3*(j/3)+2):=congrArg table (by omega)
      simp only [radix,lane,row,ite_true,k,payload,↓reduceIte, Nat.reduceMod,Nat.reduceAdd,Nat.add_zero]
      simp only [v,Nat.add_zero] <;> rfl
  · have cases2 : j%2=0 ∨ j%2=1:=by omega
    rcases cases2 with k|k
    · have v : table j=table (2*(j/2)+0):=congrArg table (by omega)
      simp only [radix,lane,row,if_neg z,k,payload,Late.parentBlock,↓reduceIte,Nat.reduceMod,Nat.reduceAdd,Nat.add_zero]
      simp only [v,Nat.add_zero] <;> rfl
    · have v : table j=table (2*(j/2)+1):=congrArg table (by omega)
      simp only [radix,lane,row,if_neg z,k,payload,Late.parentBlock,↓reduceIte,Nat.reduceMod,Nat.reduceAdd,Nat.add_zero]
      simp only [v,Nat.add_zero] <;> rfl

theorem trueStep (p : Profile) (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree p H m s t) (i : Index) (h : Nat) (lim : h<24) :
    retained p (h+1) (H (payload (lane h (nodeIndex i.val h)) (node t h (nodeIndex i.val h)) (truePeers t i h)))=
      node t (h+1) (nodeIndex i.val (h+1)) := by
  rw [tree.parent h lim _ (indexInside i (h+1))]
  apply congrArg (fun b=>retained p (h+1) (H b))
  simpa only [truePeers,sibling,childPos,nextIndex,Nat.add_zero,Nat.add_assoc] using rotated h (nodeIndex i.val h) (node t h)

theorem honestRecord (p : Profile) (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree p H m s t) (v : View) (r n : Nat) (limit : n≤24)
    (salt : v.salt r=s (v.idx r)) (value : v.entry r=m (v.idx r))
    (peers : ∀ h<n,v.peers r h=truePeers t (v.idx r) h) :
    recordAt p H v r n (v.peers r)=node t n (nodeIndex (v.idx r).val n) := by
  induction n with
  | zero=>change Late.leaf H _ _ _=node t 0 _
          rw [salt,value];simpa only [nodeIndex,span,Nat.div_one] using (tree.leaf (v.idx r)).symm
  | succ n ih=>
    change retained p (n+1) (H (payload _ (recordAt p H v r n _) _))=_
    rw [ih (by omega) (fun h bh=>peers h (by omega)),peers n (by omega)]
    exact trueStep p H m s t tree (v.idx r) n (by omega)
end CommitGolfCandidate.S4
