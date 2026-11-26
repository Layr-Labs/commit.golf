import CommitGolfCandidate.S5Witness
namespace CommitGolfCandidate.S5.Auth
open CommitGolf
open CommitGolfCandidate.S4 (nodeIndex radix width span nextIndex)
open Late (Digest Salt Block)
/-- The full ternary bottom accepts any 96-byte row. All higher rows authenticate
the low two 32-byte children using the physical height's domain and schedule. -/
def compressRow (H : Compression) (level : Nat) (row : Block) : Digest :=
  if level=1 then H row else
    Chained.parentDigest H (height (level-1)) (row.extractLsb' 0 256) (row.extractLsb' 256 256)

structure View where
  idx : Nat → Index
  entry : Nat → Entry
  salt : Nat → Salt
  peers : Nat → Nat → Peers
  slot : Nat → Digest

def walk (H : Compression) (i : Nat) (v : Digest) (data : Nat→Peers) : Nat → Digest
  | 0=>v
  | k+1=>compressRow H (k+1) ((payload (lane k (nodeIndex i k)) (walk H i v data k) (data k)))

def recordAt (H : Compression) (v : View) (j n : Nat) (data : Nat→Peers) :=
  walk H (v.idx j).val (Late.leaf H ((v.idx j).val.testBit 0) (v.salt j) (v.entry j)) data n

def lower (H : Compression) (v : View) (r : Nat) := recordAt H v r 15 (v.peers r)
def bucket (v : View) (r : Nat) := nodeIndex (v.idx r).val 15
def select (v : View) (table : Nat→Digest) (u : Nat) :=
  ((List.range 128).find? fun r=>bucket v r==u).map table

def pairChildren (v : View) (tab : Nat→Digest) (j : Nat) :=
  (select v tab (2*j),select v tab (2*j+1))
def mergePair (H : Compression) (l r : Option Digest) (slot : Digest) :=
  if l.isNone && r.isNone then slot else compressRow H 16 ((Late.parentBlock (l.getD slot) (r.getD slot)))
def pairAt (H : Compression) (v : View) (tab : Nat→Digest) (j : Nat) :=
  let (l,r):=pairChildren v tab j
  mergePair H l r (v.slot j)

def upper (H : Compression) (cap : Nat→Digest) : Nat → Nat → Digest
  | 0,i=>if i<171 then cap i else 0
  | k+1,i=>if i<width (17+k) then
      compressRow H (17+k) ((Late.parentBlock (upper H cap k (2*i)) (upper H cap k (2*i+1)))) else 0

def batchCap (H : Compression) (v : View) := pairAt H v (lower H v)
def batchRoot (H : Compression) (v : View) := upper H (batchCap H v) 8 0

def batchPeers (H : Compression) (v : View) (r n : Nat) : Peers :=
  let i:=(v.idx r).val
  if n<15 then v.peers r n else
  if n=15 then
    let x:=bucket v r
    ((select v (lower H v) (2*(x/2)+(1-x%2))).getD (v.slot (x/2)),0)
  else
    let ix:=nodeIndex i n
    (upper H (batchCap H v) (n-16) (2*(ix/2)+(1-ix%2)),0)

def BatchValid (H : Compression) (v : View) (root : Digest) :=
  (∀ r<128,select v (lower H v) (bucket v r)=some (lower H v r)) ∧ batchRoot H v=root

theorem walk_congr (H : Compression) (i : Nat) (v : Digest) (a b : Nat→Peers) (n : Nat)
    (eqn : ∀ j<n,a j=b j) : walk H i v a n=walk H i v b n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [walk,walk,eqn n (by omega),ih (fun j hj=>eqn j (by omega))]

theorem recordLower (H : Compression) (v : View) (r : Nat) :
    recordAt H v r 15 (batchPeers H v r)=lower H v r := by
  apply walk_congr;intro j hj;simp only [batchPeers,if_pos hj]

theorem binaryPayload (n i : Nat) (pos : 0<n) (get : Nat→Digest) :
    payload (lane n i) (get i) (get (2*(i/2)+(1-i%2)),0) = Late.parentBlock (get (2*(i/2))) (get (2*(i/2)+1)) := by
  unfold lane
  rw [if_neg (by omega : n≠0)]
  by_cases even : i%2=0
  · rw [if_pos even];simp only [payload,even,Nat.sub_zero,show 2*(i/2)=i by omega]
  · rw [if_neg even];have odd : i%2=1:=by omega
    simp only [payload,odd,Nat.sub_self,Nat.add_zero,show 2*(i/2)+1=i by omega]

theorem indexInside (i : Index) (h : Nat) : nodeIndex i.val h<width h := by
  have pos : 0<span h:=by cases h <;> simp [span] <;> positivity
  unfold nodeIndex width
  exact (Nat.div_lt_iff_lt_mul pos).mpr (by
    have bound:=i.isLt
    have all:=Nat.mod_add_div (LENGTH+span h-1) (span h)
    have rem:=Nat.mod_lt (LENGTH+span h-1) pos
    rw [Nat.mul_comm];omega)

private theorem capStep (H : Compression) (v : View) (r : Nat)
    (agree : select v (lower H v) (bucket v r)=some (lower H v r)) :
    recordAt H v r 16 (batchPeers H v r)=batchCap H v (nodeIndex (v.idx r).val 16) := by
  let x:=bucket v r
  let k:=x/2
  have parent : nodeIndex (v.idx r).val 16=k:=nextIndex _ 15
  have child:=recordLower H v r
  change compressRow H 16 ((payload (lane 15 x) (recordAt H v r 15 _) _))=_
  rw [child,parent]
  unfold batchPeers batchCap pairAt pairChildren mergePair
  change compressRow H 16 ((payload (if x%2=0 then .bl else .br) _ ((select v (lower H v) (2*k+(1-x%2))).getD (v.slot k),0)))=_
  by_cases even : x%2=0
  · have l : 2*k=x:=by dsimp [k];omega
    rw [if_pos even,l,show select v (lower H v) x=some _ from agree]
    simp [even,payload]
  · have rgt : 2*k+1=x:=by dsimp [k];omega
    rw [if_neg even,rgt,show select v (lower H v) x=some _ from agree]
    simp [show x%2=1 by omega,payload]

theorem batchImpliesRoot (H : Compression) (v : View) (root : Digest) (good : BatchValid H v root)
    (r : Nat) (inside : r<128) : recordAt H v r 24 (batchPeers H v r)=root := by
  let i:=(v.idx r).val
  have layer (k : Nat) (lim : k≤8) :
      recordAt H v r (16+k) (batchPeers H v r)=upper H (batchCap H v) k (nodeIndex i (16+k)) := by
    induction k with
    | zero=>
      have cap : nodeIndex i 16<171:=indexInside (v.idx r) 16
      rw [Nat.add_zero,upper,if_pos cap];exact capStep H v r (good.1 r inside)
    | succ k ih=>
      let j:=nodeIndex i (16+k)
      have nc : nodeIndex i (16+(k+1))=j/2:=by rw [show 16+(k+1)=(16+k)+1 by omega,nextIndex];change _/(radix (16+k))=_;rw [show radix (16+k)=2 from if_neg (by omega)]
      have valid := indexInside (v.idx r) (16+(k+1))
      change compressRow H (16+(k+1)) ((payload (lane (16+k) j) (recordAt H v r (16+k) _) (batchPeers H v r (16+k))))=_
      rw [ih (by omega),upper,if_pos (show nodeIndex i (16+(k+1))<width (17+k) from by simpa only [show 17+k=16+(k+1) by omega] using valid),nc]
      have peer : batchPeers H v r (16+k)=(upper H (batchCap H v) k (2*(j/2)+(1-j%2)),0) := by
        simp [batchPeers,j,i,show ¬16+k<15 by omega,show 16+k≠15 by omega]
      rw [peer,show 16+(k+1)=17+k by omega]
      exact congrArg (fun x=>compressRow H (17+k) (x)) (binaryPayload (16+k) j (by omega) _)
  have z : nodeIndex i 24=0:=by have h : nodeIndex i 24<1:=indexInside (v.idx r) 24;omega
  exact (layer 8 (by decide)).trans (by change upper _ _ 8 (nodeIndex i 24)=_;rw [z];exact good.2)
end CommitGolfCandidate.S5.Auth
