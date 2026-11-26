import CommitGolfCandidate.S5ReplayRecord
namespace CommitGolfCandidate.S5.Replay
open CommitGolf
open Chained (Output parentDigest)
open Late (Digest)
abbrev Table := Nat→Output
abbrev Levels := Nat→Table
def lowerTable (v : Auth.View) : Code (128*recordCost 14) Table :=
  tabulate 0 (fun r=>recordCode v r (v.peers r) 14) 128
private theorem lookup_eq (v : Auth.View) (a b : Table) (agree : ∀ r<128,a r=b r) (j : Nat) :
    Auth.select v a j=Auth.select v b j := by
  unfold Auth.select
  cases e : (List.range 128).find? (fun r=>Auth.bucket v r==j)
  · rfl
  next r=>exact congrArg some (agree r (List.mem_range.mp (List.mem_of_find?_eq_some e)))

private theorem upper_hash (H : Compression) (n : Nat) (l r : Output) (pos : 0<n) :
    Auth.compressRow H (n+1) (Late.parentBlock l r)=parentDigest H (height n) l r := by
  have row : Auth.row n l r 0=Late.parentBlock l r:=by unfold Auth.row;split <;> rfl
  rw [←row,Auth.row_parent];cases n <;> first | omega | rfl
private theorem maximum (h : Chained.Height) : Chained.calls h≤16:=(by decide +kernel : ∀ k : Chained.Height,Chained.calls k≤16) h
def pairCode (v : Auth.View) (tab : Table) (j : Nat) : Code 16 Output :=
  let left:=Auth.select v tab (2*j)
  let right:=Auth.select v tab (2*j+1)
  if left.isNone && right.isNone then widen (done (v.slot j)) (by decide)
  else widen (parentCode (height 15) (left.getD (v.slot j)) (right.getD (v.slot j))) (maximum _)
private theorem pair_value (H : Compression) (v : Auth.View) (tab : Table) (j : Nat) :
    (pairCode v tab j).value H=Auth.pairAt H v tab j := by
  unfold pairCode Auth.pairAt Auth.pairChildren Auth.mergePair
  dsimp only;split
  · rfl
  · exact (parent_values H _ _ _).1.trans (upper_hash H 15 _ _ (by decide)).symm

def firstCap (v : Auth.View) (tab : Table) :=tabulate 0 (pairCode v tab) 171
def upperCell (h : Nat) (pr : Table) (j : Nat) : Code 16 Output :=
  if j<S4.width (17+h) then widen (parentCode (height (16+h)) (pr (2*j)) (pr (2*j+1))) (maximum _)
  else widen (done 0) (by decide)
def history (cap : Table) : (k : Nat)→Code (k*(171*16)) Levels
  | 0=>widen (done (fun _=>cap)) (by decide)
  | k+1=>widen (join (history cap k) (fun prev=>map (fun latest h=>if h=k+1 then latest else prev h)
      (tabulate 0 (upperCell k (prev k)) 171))) (by omega)
attribute [local irreducible] tabulate
set_option maxRecDepth 10000 in
private theorem history_succ (H : Compression) (cap : Table) (k h : Nat) :
    (history cap (k+1)).value H h=if h=k+1 then (tabulate 0 (upperCell k ((history cap k).value H k)) 171).value H else (history cap k).value H h := rfl
private theorem history_value (H : Compression) (cap : Table) (k : Nat) (bound : k≤8)
    (zero : ∀ i,171 ≤ i → cap i=0) : ∀ h≤k,∀ i,(history cap k).value H h i=Auth.upper H cap h i := by
  induction k with
  | zero=>
    intro h hh i;have z : h=0:=by omega
    subst h;change cap i=(if i<171 then cap i else 0)
    split <;> first | rfl | exact zero i (by omega)
  | succ k ih=>
    intro h hh i
    have prev:=ih (by omega)
    by_cases last : h=k+1
    · subst h
      rw [history_succ,if_pos rfl]
      rw [tab_value];unfold upperCell
      have lower : S4.width (17+k)≤171:=(by decide +kernel : ∀ j : Fin 8,S4.width (17+j.val)≤171) ⟨k,by omega⟩
      by_cases inside : i<S4.width (17+k)
      · rw [if_pos (by omega : i<171),if_pos inside,Auth.upper,if_pos inside]
        change (parentCode (height (16+k)) _ _).value H=_
        rw [(parent_values ..).1,prev k le_rfl,prev k le_rfl]
        rw [show 17+k=16+k+1 by omega];exact (upper_hash H (16+k) _ _ (by omega)).symm
      · rw [if_neg inside,Auth.upper,if_neg inside];split <;> rfl
    · rw [history_succ,if_neg last];exact prev h (by omega) i

def peerMap (v : Auth.View) (bottom : Table) (top : Levels) (r n : Nat) : Peers :=
  let i:=(v.idx r).val
  if n<15 then v.peers r n else if n=15 then
    let j:=Auth.bucket v r
    ((Auth.select v bottom (2*(j/2)+(1-j%2))).getD (v.slot (j/2)),0)
  else (top (n-16) (2*(S4.nodeIndex i n/2)+(1-S4.nodeIndex i n%2)),0)
def recover (v : Auth.View) : Code (128*recordCost 14+(171*16+8*(171*16))) (Nat→Nat→Peers) :=
  join (lowerTable v) (fun lower=>join (firstCap v lower) (fun cap=>map (peerMap v lower) (history cap 8)))
attribute [local irreducible] history
set_option maxRecDepth 12000 in
theorem recover_value (H : Compression) (v : Auth.View) (r h : Nat) (bound : h<24) :
    (recover v).value H r h=Auth.batchPeers H v r h := by
  let lo:=(lowerTable v).value H
  let cap:=(firstCap v lo).value H
  have lower (j : Nat) (lim : j<128) : lo j=Auth.lower H v j := by
    unfold lo lowerTable;rw [tab_value,if_pos lim];exact record_value H v j _ 14
  have agree (i : Nat) : Auth.select v lo i=Auth.select v (Auth.lower H v) i:=lookup_eq v lo _ lower i
  have table (i : Nat) : cap i=Auth.upper H (Auth.batchCap H v) 0 i := by
    unfold cap firstCap;rw [tab_value,Auth.upper];split
    · rw [pair_value,Auth.batchCap,Auth.pairAt,Auth.pairAt,Auth.pairChildren,Auth.pairChildren,agree,agree]
    · rfl
  have outside (i : Nat) (le : 171 ≤ i) : cap i=0:=by rw [table,Auth.upper,if_neg (by omega)]
  have eqtop (d : Nat) (i : Nat) : Auth.upper H cap d i=Auth.upper H (Auth.batchCap H v) d i := by
    induction d generalizing i with
    | zero=>rw [Auth.upper];split <;> first | exact table i | (rw [Auth.upper,if_neg (by omega)])
    | succ k ih=>simp only [Auth.upper,ih]
  change peerMap v lo ((history cap 8).value H) r h=_
  unfold peerMap Auth.batchPeers
  split
  · rfl
  · split
    · dsimp only;rw [agree]
    · dsimp only;rw [history_value H cap 8 le_rfl outside (h-16) (by omega),eqtop]
end CommitGolfCandidate.S5.Replay
