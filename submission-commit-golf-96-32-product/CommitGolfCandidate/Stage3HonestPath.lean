import CommitGolfCandidate.Stage3HonestPacking
import CommitGolfCandidate.TruncAuthentication
namespace CommitGolfCandidate.Trunc
open CommitGolf
private theorem finRead {α : Type} (n : Nat) (f : Fin n → α) (j : Fin n) (v : α) :
    ((List.finRange n).map f)[j.val]?.getD v=f j := by
  have hi : j.val<(List.finRange n).length := by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_finRange,Option.map_some,Option.getD_some]
  congr 1

theorem recordOrdinal (x : CheckInput) (r : Nat) (hr : r<x.positions.card) :
    recordIndex x r=Late.Check.recordIndex x.positions r := by
  apply Fin.ext
  simp only [recordIndex,openingIndex,dif_pos hr,Late.Check.recordIndex,
    List.getElem?_eq_getElem (by simpa using hr : r<(x.positions.sort (·≤·)).length),Option.getD_some]

theorem recordEntry (x : CheckInput) (r : Nat) (hr : r<x.positions.card) :
    recordValue x r=Late.Check.recordValue x r := by
  simp only [recordValue,dif_pos hr,Late.Check.recordValue,List.getElem?_eq_getElem
    (by simpa using hr : r<(x.positions.attach.sort (fun a b=>a.val≤b.val)).length),Option.map_some,Option.getD_some]

attribute [local irreducible] Late.treeM Late.node List.finRange

theorem widePath (H : Compression) (m : Message) (salt : Late.SaltTape) (ps : Positions) (r d : Nat)
    (hr : r<ps.card) (bound : d≤LOG_LENGTH) (parsed : d≤Late.Check.depth (Late.Check.canonicalInput m ps (Late.treeM (M:=Id) H m salt) salt)) :
    let t:=Late.treeM (M:=Id) H m salt
    let x:=Late.Check.canonicalInput m ps t salt
    let i:=recordIndex x r
    recordAncestor H d (recordValue x r) (Late.Check.salt x r) i (Late.Check.sibling x r)=
      Late.node t d (Late.Open.indexAbove i d) := by
  let t:=Late.treeM (M:=Id) H m salt
  let x:=Late.Check.canonicalInput m ps t salt
  let i:=Late.Check.recordIndex ps r
  let base : Nat → Digest := fun k=>(Late.initialList H m salt)[k]?.getD 0
  let hp:=referenceHeap H LENGTH base
  have ix : recordIndex x r=i :=recordOrdinal _ _ hr
  have val : recordValue x r=m i := (recordEntry _ _ hr).trans (Late.Check.honestValue m ps t salt r hr)
  have first : hp (LENGTH+i.val)=leafDigest H i (salt i) (m i) := by
    apply (reference_heap_leaf H LENGTH base i.val i.isLt).trans
    exact finRead LENGTH (fun i=>Late.leaf H (i.val.testBit 0) (salt i) (m i)) i 0
  have path : recordPathPrefix d i (Late.Check.sibling x r)=heapPath hp (LENGTH+i.val) d := by
    apply List.ext_getElem
    · rw [record_path_prefix_length,heap_path_length]
    · intro j h1 h2
      have hj : j<d := by simpa only [record_path_prefix_length] using h1
      have lo : j<LOG_LENGTH := by omega
      rw [heap_path_get hp (LENGTH+i.val) d j hj]
      simp only [recordPathPrefix,List.getElem_map,List.getElem_range]
      refine Prod.ext (heap_leaf_direction 24 i.val j i.isLt lo).symm ?_
      have sr:=Late.Check.honest_sibling m ps t salt r j hr (hj.trans_le parsed)
      rw [Late.siblingHeap i j lo]
      exact sr.trans (Late.heapLevel H m salt j _ (by omega) (Late.Open.mate_bound _ _ lo))
  have parents (n : Nat) (pos : 0<n) (below : n<LENGTH) : hp n=parent H n (hp (2*n)) (hp (2*n+1)) :=
    reference_heap_parent H LENGTH base n pos below
  have enough : 2^d≤LENGTH+i.val := (Nat.pow_le_pow_right (by decide) bound).trans (Nat.le_add_right LENGTH i.val)
  have ans:=reconstruct_heap_ancestor H hp LENGTH parents d (LENGTH+i.val) (by have :=i.isLt;omega) enough
  rw [Late.aboveHeap _ _ bound] at ans
  change recordAncestor H d (recordValue x r) (Late.Check.salt x r) (recordIndex x r) _=_
  rw [ix,val,Late.Check.honest_salt m ps t salt r hr,recordAncestor,path,←first]
  exact ans.trans (Late.heapLevel H m salt d _ bound (Late.Open.above_bound i d bound)).symm
end CommitGolfCandidate.Trunc
