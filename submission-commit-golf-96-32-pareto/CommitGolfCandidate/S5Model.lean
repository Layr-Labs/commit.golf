import CommitGolfCandidate.Stage3cParent
import CommitGolfCandidate.S4Geometry
import CommitGolfCandidate.LateModel
namespace CommitGolfCandidate.S5
open CommitGolf OracleComp
open Chained (Height Output Input Seed)
open Late (Levels Digest SaltTape)

def height (d : Nat) : Height := ⟨d%24,by omega⟩
def bits : Nat→Nat | 0=>256 | n+1=>Chained.wireWidth (height n)
def chainM {M : Type→Type} [Monad M] (hash : Input → M Output) (h : Height) (seed : Seed) : Nat→M Output
  | 0=>hash (Chained.pack (.inl (Chained.workClass h,seed)))
  | j+1=>do let x←chainM hash h seed j; hash (Chained.encodeNext (Chained.workClass h) (j+1) x)

def parentM {M : Type→Type} [Monad M] (hash : Input→M Output) (d : Nat) (ns : List Digest) (j : Nat) : M Output :=
  let i:=S4.radix d*j
  let left:=ns[i]?.getD 0
  let right:=ns[i+1]?.getD 0
  if d=0 then hash (ns[i+2]?.getD 0 ++ right ++ left) else do
    let h:=height d
    let v←chainM hash h (right++left) (Chained.calls h-1)
    pure (Chained.storeReply h v)

def parentsM {M : Type→Type} [Monad M] (hash : Input→M Output) (d : Nat) (ns : List Digest) :=
  (List.range (S4.width (d+1))).mapM (parentM hash d ns)

def levelsM {M : Type→Type} [Monad M] (hash : Input→M Output) : Nat→List Digest→M Levels
  | 0, ns=>pure [ns]
  | d+1, ns=>do let upper←parentsM hash (23-d) ns;return ns::(←levelsM hash d upper)

def treeM {M : Type→Type} [Monad M] (hash : Input→M Output) (m : Message) (s : SaltTape) : M Levels := do
  let leaves←(List.finRange LENGTH).mapM fun i=>Late.leafM hash (i.val.testBit 0) (s i) (m i)
  levelsM hash 24 leaves

abbrev Field := Nat × Nat
def record (t : Levels) (s : SaltTape) (i : Index) (batch : Bool) : List Field :=
  (192,(s i).toNat)::(List.range (if batch then 15 else 24)).flatMap fun d=>
    (List.range (S4.radix d-1)).map fun n=>
      let j:=S4.radix d*S4.nodeIndex i.val (d+1)+(S4.childPos i d+n+1)%S4.radix d
      (if batch then bits d else 256,(Late.node t d j).toNat)

def slot (t : Levels) (xs : List Index) (j : Nat) : Field :=
  let l:=xs.any fun i=>S4.nodeIndex i.val 15==2*j
  let r:=xs.any fun i=>S4.nodeIndex i.val 15==2*j+1
  (230,(if l || r then Late.node t 15 (2*j+(if l && !r then 1 else 0)) else Late.node t 16 j).toNat)

def encode : List Field→Nat
  | []=>0
  | (w,v)::rest=>v%2^w + 2^w*encode rest

def opening (t : Levels) (s : SaltTape) (ps : Positions) : Proof :=
  let xs:=ps.sort (·≤·)
  if ps.card=BATCH then
    let data:=encode (xs.flatMap (fun i=>record t s i true)++(List.range 171).map (slot t xs))
    (List.range 69396).map fun j=>BitVec.ofNat 8 (data/2^(8*j))
  else
    xs.flatMap fun i=>(record t s i false).flatMap fun (w,v)=>(List.range (w/8)).map fun j=>BitVec.ofNat 8 (v/2^(8*j))

def scheme (check : Late.Checker) : Scheme where
  Trapdoor:=Levels × SaltTape
  commit m:=do let s←Late.sampleSalts;let t←treeM Late.hash m s;return (Late.node t LOG_LENGTH 0,t,s)
  opening td ps:=pure (opening td.1 td.2 ps)
  check:=check

def parentCost : Nat→Nat
  | 0=>0
  | d+1=>S4.width (23-d+1)*Chained.calls (height (23-d))+parentCost d

theorem parent_cost : parentCost 24=11318830 := by decide +kernel
theorem parentAllowance : parentCost 24≤LENGTH := by rw [parent_cost];decide
theorem wire_geometry :
    let recordBits:=192+((List.range 15).map (fun d=>(S4.radix d-1)*bits d)).sum
    128*recordBits+171*230=8*69396+2 := by decide +kernel

theorem opening_congr (t : Levels) (a b : SaltTape) (ps : Positions) (same : ∀ i∈ps,a i=b i) :
    opening t a ps=opening t b ps := by
  have field (i : Index) (hi : i∈ps.sort (·≤·)) (mode : Bool) : record t a i mode=record t b i mode := by
    unfold record;rw [same i (by simpa only [Finset.mem_sort] using hi)]
  have batch : (ps.sort (·≤·)).flatMap (fun i=>record t a i true)=(ps.sort (·≤·)).flatMap (fun i=>record t b i true) := by
    rw [List.flatMap_def,List.flatMap_def];congr 1;apply List.map_congr_left;exact fun i hi=>field i hi true
  simp only [opening]
  split
  · rw [batch]
  · rw [List.flatMap_def,List.flatMap_def];congr 1;apply List.map_congr_left
    intro i hi;rw [field i hi false]
end CommitGolfCandidate.S5
