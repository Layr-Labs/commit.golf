import CommitGolfCandidate.RungAInterface
import CommitGolfCandidate.LateCachedTree
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace CommitGolfCandidate.RungA
open CommitGolf
open Late (node levelCount)
def leafAt (o : Oracle) (m : Message) (r : Tape) (j : Nat) : Late.Digest :=
  (Late.initialList o.compression m (R4.pairSalts r))[j]?.getD 0
private theorem finLookup {n : Nat} (f : Fin n→Late.Digest) (j : Fin n) :
    ((List.finRange n).map f)[j.val]?.getD 0=f j := by
  have mem : j.val<(List.finRange n).length:=by simpa only [List.length_finRange] using j.isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem mem,List.getElem_finRange,Option.map_some,Option.getD_some]
  exact congrArg f (Fin.ext rfl)
attribute [local irreducible] List.finRange List.map
theorem leafAt_eq (o : Oracle) (m : Message) (r : Tape) (i : Index) :
    leafAt o m r i.val=o.compression (finalRow o m r i) := by
  unfold leafAt Late.initialList LateHiding.leafLayer finalRow
  exact finLookup (fun i : Index=>LateHiding.leafDigest o.compression (i.val.testBit 0) (R4.pairSalts r i) (m i)) i
theorem refNode (o : Oracle) (m : Message) (r : Tape) (h j : Nat) (b : h≤24) :
    node (tree o m r) h j=Late.treeNode o.compression (leafAt o m r) h j :=
  Late.fixed_tree_node_all o.compression m (R4.pairSalts r) h j b

def physicalLane (H : Compression) (td : Late.Trapdoor) (h j k : Nat) : Late.Digest :=
  if k<S4.radix h ∧ S4.radix h*j+k<levelCount h then rebuildDigest H td h (S4.radix h*j+k)
  else Late.slice td (Late.unusedSlotAddr h j k) 32
def joined (f : Nat→Late.Digest) : Late.Block := f 2 ++ f 1 ++ f 0
theorem r0 (H : Compression) (td : Late.Trapdoor) (j : Nat) :
    rebuildDigest H td 0 j=(if j<levelCount 0 then H (Late.slice td (finalRowAddress j) 96) else 0) := rfl
theorem rn (H : Compression) (td : Late.Trapdoor) (h j : Nat) :
    rebuildDigest H td (h+1) j=(if j<levelCount (h+1) then S4.retained S4.active (h+1) (H (joined (physicalLane H td h j))) else 0) := rfl
theorem t0 (H : Compression) (base : Nat→Late.Digest) (j : Nat) :
    Late.treeNode H base 0 j=(if j<levelCount 0 then base j else 0):=rfl
theorem tn (H : Compression) (base : Nat→Late.Digest) (h j : Nat) :
    Late.treeNode H base (h+1) j=(if j<levelCount (h+1) then S4.retained S4.active (h+1) (H
      (S4.row h (Late.treeNode H base h (S4.radix h*j)) (Late.treeNode H base h (S4.radix h*j+1))
         (Late.treeNode H base h (S4.radix h*j+2)))) else 0):=rfl
end CommitGolfCandidate.RungA
