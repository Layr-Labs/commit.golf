import CommitGolfCandidate.S5Auth
import CommitGolfCandidate.S5CachedTree

namespace CommitGolfCandidate.S5.Auth
open CommitGolf
open S4 (width radix span nodeIndex nextIndex childPos)
open Late (Digest SaltTape Levels node)

def row (d : Nat) (a b c : Digest) : Late.Block := (if d=0 then c else 0) ++ b ++ a
def sibling (t : Levels) (i h n : Nat) : Digest :=
  Late.node t h (radix h*nodeIndex i (h+1)+(childPos i h+n+1)%radix h)

theorem row_parent (H : Compression) (d : Nat) (a b c : Digest) :
    compressRow H (d+1) (row d a b c)=S5Machine.nodeHash H d a b c := by
  cases d with
  | zero=>rfl
  | succ d=>
    have lo : (row (d+1) a b c).extractLsb' 0 256=a := BitVec.extractLsb'_append_eq_right
    have mid : (row (d+1) a b c).extractLsb' 256 256=b := by
      have middle (z a b : BitVec 256) : (z++b++a).extractLsb' 256 256=b :=
        (BitVec.extractLsb'_append_eq_of_le (xhi:=z++b) (xlo:=a) (start:=256) (len:=256) le_rfl).trans
          BitVec.extractLsb'_append_eq_right
      exact middle _ a b
    simp [compressRow,S5Machine.nodeHash,lo,mid]
structure HonestTree (H : Compression) (m : Message) (s : SaltTape) (t : Levels) : Prop where
  leaf : ∀ i : Index,node t 0 i.val=Late.leaf H (i.val.testBit 0) (s i) (m i)
  parent : ∀ h<24,∀ j < width (h+1),node t (h+1) j=compressRow H (h+1) ((row h
    (node t h (radix h*j)) (node t h (radix h*j+1)) (node t h (radix h*j+2))))
  missing : ∀ h≤24,∀ j,width h≤j → node t h j=0

attribute [local irreducible] List.finRange S5Machine.treeNode

private theorem finLookup {α : Type} (n : Nat) (f : Fin n→α) (i : Fin n) (z : α) :
    ((List.finRange n).map f)[i.val]?.getD z=f i := by
  have b : i.val<(List.finRange n).length:=by rw [List.length_finRange];exact i.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem b,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

private theorem initialLeaf (H : Compression) (m : Message) (s : SaltTape) (i : Index) :
    (S5Machine.initialList H m s)[i.val]?.getD 0=Late.leaf H (i.val.testBit 0) (s i) (m i) := by
  unfold S5Machine.initialList LateHiding.leafLayer
  exact (finLookup LENGTH (fun j=>LateHiding.leafDigest H (j.val.testBit 0) (s j) (m j)) i 0).trans
    (LateHiding.leaf_digest_eq ..)

theorem honestTree (H : Compression) (m : Message) (s : SaltTape) : HonestTree H m s (S5Hiding.tree H m s) := by
  let base : Nat→Digest:=fun k=>(S5Machine.initialList H m s)[k]?.getD 0
  have eqn (h j : Nat) (limit : h≤24) : node (S5Hiding.tree H m s) h j=S5Machine.treeNode H base h j :=
    S5Machine.fixed_tree_node_all _ _ _ _ _ limit
  have count (h : Nat) (b : h≤24) : S5Machine.levelCount h=width h:=by unfold S5Machine.levelCount;rw [Nat.min_eq_left b]
  constructor
  · intro i
    rw [eqn 0 i.val (by decide),S5Machine.treeNode]
    exact (if_pos i.isLt).trans (initialLeaf H m s i)
  · intro h bh j bj
    simp only [eqn h _ (by omega),eqn (h+1) _ (by omega)]
    rw [S5Machine.treeNode]
    rw [row_parent]
    exact if_pos (by rwa [count _ (by omega)] : j<S5Machine.levelCount (h+1))
  · intro h bh j out
    rw [eqn h j bh];exact S5Machine.missing_node _ _ _ _ ((count h bh).symm ▸ out)

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

theorem trueStep (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree H m s t) (i : Index) (h : Nat) (lim : h<24) :
    compressRow H (h+1) ((payload (lane h (nodeIndex i.val h)) (node t h (nodeIndex i.val h)) (truePeers t i h)))=
      node t (h+1) (nodeIndex i.val (h+1)) := by
  rw [tree.parent h lim _ (indexInside i (h+1))]
  apply congrArg (compressRow H (h+1))
  simpa only [truePeers,sibling,childPos,nextIndex,Nat.add_zero,Nat.add_assoc] using rotated h (nodeIndex i.val h) (node t h)

theorem honestRecord (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree H m s t) (v : View) (r n : Nat) (limit : n≤24)
    (salt : v.salt r=s (v.idx r)) (value : v.entry r=m (v.idx r))
    (peers : ∀ h<n,v.peers r h=truePeers t (v.idx r) h) :
    recordAt H v r n (v.peers r)=node t n (nodeIndex (v.idx r).val n) := by
  induction n with
  | zero=>change Late.leaf H _ _ _=node t 0 _
          rw [salt,value];simpa only [nodeIndex,span,Nat.div_one] using (tree.leaf (v.idx r)).symm
  | succ n ih=>
    change compressRow H (n+1) ((payload _ (recordAt H v r n _) _))=_
    rw [ih (by omega) (fun h bh=>peers h (by omega)),peers n (by omega)]
    exact trueStep H m s t tree (v.idx r) n (by omega)
end CommitGolfCandidate.S5.Auth
