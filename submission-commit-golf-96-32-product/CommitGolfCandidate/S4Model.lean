import CommitGolfCandidate.S4Geometry
import CommitGolfCandidate.LateModel

namespace CommitGolfCandidate.S4
open CommitGolf OracleComp
open Late (Digest Block Salt SaltTape Levels)

def retained (p : Profile) (h : Nat) (x : Digest) : Digest :=
  if bits p h=238 then (0 : BitVec 18) ++ x.extractLsb' 0 238
  else if bits p h=240 then (0 : BitVec 16) ++ x.extractLsb' 0 240 else x

def row (h : Nat) (a b c : Digest) : Block := (if h=0 then c else 0) ++ b ++ a
def readRow (h : Nat) (nodes : List Digest) (p : Nat) : Block :=
  let i:=radix h*p
  row h (nodes[i]?.getD 0) (nodes[i+1]?.getD 0) (nodes[i+2]?.getD 0)

def parentsM {M : Type → Type} [Monad M] (p : Profile) (H : Block → M Digest) (h : Nat) (ns : List Digest) :
    M (List Digest) :=
  (List.range (width (h+1))).mapM (fun j=>do return retained p (h+1) (←H (readRow h ns j)))

def levelsM {M : Type → Type} [Monad M] (p : Profile) (H : Block → M Digest) : Nat → List Digest → M Levels
  | 0,ns => pure [ns]
  | d+1,ns => do
    let upper ← parentsM p H (23-d) ns
    let tail ← levelsM p H d upper
    return ns::tail

def treeM {M : Type → Type} [Monad M] (p : Profile) (H : Block → M Digest) (m : Message) (s : SaltTape) : M Levels := do
  let leaves ← (List.finRange LENGTH).mapM fun i=>Late.leafM H (i.val.testBit 0) (s i) (m i)
  levelsM p H 24 leaves

def sibling (t : Levels) (i h n : Nat) : Digest :=
  Late.node t h (radix h * nodeIndex i (h+1) + (childPos i h+n+1)%radix h)

def pairSlot (t : Levels) (positions : List Index) (j : Nat) : Digest :=
  match positions.find? (fun i=>nodeIndex i.val 16==j) with
  | none=>Late.node t 16 j
  | some i=>sibling t i.val 15 0

/-- A field carries its bit width and its little-endian value. -/
abbrev Field := Nat × Digest
def record (p : Profile) (batch : Bool) (t : Levels) (s : SaltTape) (i : Index) : List Field :=
  (192,(s i).setWidth 256) :: (List.range (if batch then 15 else 24)).flatMap fun h=>
    (List.range (radix h-1)).map fun n=>(if batch then bits p h else 256,sibling t i.val h n)

def mainBytes (x : Field) : List Byte := (List.range (x.1/8)).map fun j=>x.2.extractLsb' (8*j) 8
def sideValue (v : Digest) : Nat := (v.extractLsb' 232 6).toNat
def serialize (fields : List Field) : Proof :=
  let tails := (fields.filter fun f=>f.1==238).map (fun f=>sideValue f.2)
  fields.flatMap mainBytes ++ (List.range ((6*tails.length+7)/8)).map fun j=>
    let k:=8*j/6
    let shift:=8*j%6
    let pair:=tails[k]?.getD 0+64*tails[k+1]?.getD 0
    BitVec.ofNat 8 (pair/2^shift)

def opening (p : Profile) (t : Levels) (s : SaltTape) (pos : Positions) : Proof :=
  let indices:=pos.sort (·≤·)
  if pos.card=BATCH then serialize (indices.flatMap (record p true t s) ++
    (List.range 171).map fun j=>(bits p 16,pairSlot t indices j))
  else serialize (indices.flatMap (record p false t s))

def scheme (p : Profile) (check : Late.Checker) : Scheme where
  Trapdoor := Levels × SaltTape
  commit m := do
    let tape ← Late.sampleSalts
    let t ← treeM p Late.hash m tape
    return (Late.node t LOG_LENGTH 0,t,tape)
  opening td ps := pure (opening p td.1 td.2 ps)
  check := check

theorem opening_salt_congr (p : Profile) (t : Levels) (s z : SaltTape) (ps : Positions)
    (eqv : ∀ i∈ps,s i=z i) : opening p t s ps=opening p t z ps := by
  have same (b : Bool) : (ps.sort (·≤·)).flatMap (record p b t s)=(ps.sort (·≤·)).flatMap (record p b t z) := by
    rw [List.flatMap_def,List.flatMap_def];congr 1;apply List.map_congr_left
    intro i hi;unfold record;rw [eqv i (by simpa only [Finset.mem_sort] using hi)]
  unfold opening;simp only [same]
end CommitGolfCandidate.S4
