import CommitGolfCandidate.S4RecordReplay

set_option Elab.async false

namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Digest)
open Queries (join done query table retime)

def lowerTable (p : Profile) (v : View) : Queries (128*19) (Nat→Digest) :=
  table (fun r=>Queries.map Prod.fst (replayRecord p v r (v.peers r) 15)) 128

theorem selectCongr (v : View) (a b : Nat→Digest) (u : Nat) (eqv : ∀ r<128,a r=b r) :
    select v a u=select v b u := by
  unfold select
  cases e : (List.range 128).find? (fun r=>bucket v r==u) with
  | none=>rfl
  | some r=>rw [Option.map_some,Option.map_some,eqv r (List.mem_range.mp (List.mem_of_find?_eq_some e))]

theorem lowerSelect (p : Profile) (v : View) (o : Oracle) (u : Nat) :
    select v ((lowerTable p v).eval o) u=select v (lower p o.compression v) u := by
  apply selectCongr
  intro r hr
  simp only [lowerTable,Queries.tableValue,if_pos hr,Queries.map,replayValue,lower]

def mergeQuery (p : Profile) (l r : Option Digest) (slot : Digest) : Queries 1 Digest :=
  Queries.map (fun y=>if l.isNone && r.isNone then slot else retained p 16 y)
    (query (Late.parentBlock (l.getD slot) (r.getD slot)))

def capTable (p : Profile) (v : View) (tab : Nat→Digest) : Queries 171 (Nat→Digest) :=
  retime (Nat.mul_one 171) (table (fun j=>mergeQuery p (select v tab (2*j)) (select v tab (2*j+1)) (v.slot j)) 171)

theorem capValue (p : Profile) (v : View) (o : Oracle) (i : Nat) :
    (capTable p v ((lowerTable p v).eval o)).eval o i=upper p o.compression (batchCap p o.compression v) 0 i := by
  simp only [capTable,Queries.retime,Queries.tableValue,upper,mergeQuery,Queries.map,Queries.query,lowerSelect,
    batchCap,pairAt,pairChildren,mergePair] <;> rfl

def upperCost : Nat→Nat
  | 0=>0
  | k+1=>upperCost k+width (17+k)

/-- Cache every real upper node once and retain earlier rows for the selected path. -/
def upperTables (p : Profile) (cap : Nat→Digest) : (n : Nat) → Queries (upperCost n) (Nat→Nat→Digest)
  | 0=>done (fun _=>cap)
  | k+1=>join (upperTables p cap k) fun rows=>
      Queries.map (fun (t : Nat→Digest) h=>if h=k+1 then t else rows h)
        (retime (Nat.mul_one _) (table (fun j=>Queries.map (retained p (17+k))
          (query (Late.parentBlock (rows k (2*j)) (rows k (2*j+1))))) (width (17+k))))

theorem upperValue (p : Profile) (o : Oracle) (cap raw : Nat→Digest)
    (start : ∀ i,cap i=upper p o.compression raw 0 i) (n h : Nat) (bh : h≤n) (i : Nat) :
    (upperTables p cap n).eval o h i=upper p o.compression raw h i := by
  induction n generalizing h i with
  | zero=>have z : h=0:=by omega
          subst h;exact start i
  | succ k ih=>
    by_cases eqv : h=k+1
    · subst h
      simp only [upperTables,Queries.join,Queries.map,Queries.retime,ite_true,Queries.tableValue,Queries.query,
        upper,ih k (Nat.le_refl k)]
    · simp only [upperTables,Queries.join,Queries.map,if_neg eqv]
      exact ih h (by omega) i

def computedPeers (v : View) (r : Nat) (tab : Nat→Digest) (rows : Nat→Nat→Digest) (n : Nat) : Peers :=
  if n<15 then v.peers r n else if n=15 then
    let x:=bucket v r
    ((select v tab (2*(x/2)+(1-x%2))).getD (v.slot (x/2)),0)
  else
    let x:=nodeIndex (v.idx r).val n
    (rows (n-16) (2*(x/2)+(1-x%2)),0)

def batchCost := 128*19+ (171+(upperCost 7+28))

def batchExtract (p : Profile) (v : View) (r : Nat) : Queries batchCost Trace :=
  join (lowerTable p v) fun tab=>
    join (capTable p v tab) fun cap=>
      join (upperTables p cap 7) fun rows=>replayRecord p v r (computedPeers v r tab rows) 24

attribute [local irreducible] lowerTable upperTables capTable replayRecord recordAt upper
set_option maxRecDepth 6000 in
theorem batchExtractValue (p : Profile) (o : Oracle) (v : View) (r : Nat) :
    (batchExtract p v r).eval o=(recordAt p o.compression v r 24 (batchPeers p o.compression v r),
      recordInputs p o.compression v r (batchPeers p o.compression v r) 24) := by
  let tab:=(lowerTable p v).eval o
  let cap:=(capTable p v tab).eval o
  let rows:=(upperTables p cap 7).eval o
  have peers (n : Nat) (lim : n<24) : computedPeers v r tab rows n=batchPeers p o.compression v r n := by
    unfold computedPeers batchPeers
    by_cases a : n<15
    · rw [if_pos a,if_pos a]
    rw [if_neg a,if_neg a]
    by_cases b : n=15
    · simp only [b,ite_true,tab,lowerSelect]
    rw [if_neg b,if_neg b]
    exact congrArg (fun x=>(x,(0 : Digest))) (upperValue p o cap (batchCap p o.compression v) (capValue p v o) 7 (n-16) (by omega) _)
  change (replayRecord p v r (computedPeers v r tab rows) 24).eval o=_
  rw [replayValue]
  have agrees (k : Nat) (bound : k≤24) : recordAt p o.compression v r k (computedPeers v r tab rows)=
      recordAt p o.compression v r k (batchPeers p o.compression v r) := by
    unfold recordAt;apply walk_congr;intro j hj;exact peers j (by omega)
  have trace (k : Nat) (bound : k≤24) : recordInputs p o.compression v r (computedPeers v r tab rows) k=
      recordInputs p o.compression v r (batchPeers p o.compression v r) k := by
    induction k with
    | zero=>rfl
    | succ k ih=>simp only [recordInputs,inputAt,agrees k (by omega),peers k (by omega),ih (by omega)]
  rw [agrees 24 (by decide),trace 24 (by decide)]

theorem batchCost_le : batchCost≤5436 := by decide
end CommitGolfCandidate.S4
