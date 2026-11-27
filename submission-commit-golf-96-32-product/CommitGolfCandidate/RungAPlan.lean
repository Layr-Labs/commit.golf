import CommitGolfCandidate.R4LaneCode
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA.Kernel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

inductive Term where
  | old (slot : Nat)
  | zero
  | leaf (index : Nat)
  | hash (short : Bool) (left right third : Term)
  deriving DecidableEq, Repr

def mask (b : Bool) (v : Late.Digest) := if b then Trunc.padLow v else v
def value (H : Compression) (leaves saved : Nat→Late.Digest) : Term → Late.Digest
  | .old j=>saved j
  | .zero=>0
  | .leaf j=>leaves j
  | .hash b l r t=>mask b (H (value H leaves saved t ++ value H leaves saved r ++ value H leaves saved l))

inductive Source where
  | leaf (j : Nat)
  | scratch (slot : Nat)
  deriving DecidableEq, Repr
inductive Dest where
  | scratch (slot : Nat)
  | output
  deriving DecidableEq, Repr
inductive Act where
  | clear (slot : Nat)
  | call (src : Source) (dst : Dest) (assign short : Bool)
  deriving DecidableEq, Repr

def signedRow (j : Nat) := BitVec.ofInt 12 ((184*(j/2)+88*(j%2) : Nat) - (1920 : Int))
def sourceOp : Source → Instr
  | .leaf j=>.ADDI .x10 .x21 (signedRow j)
  | .scratch n=>.ADDI .x10 .x0 (BitVec.ofNat 12 (32*n))
def destOp (off : Nat) : Dest → Instr
  | .scratch n=>.ADDI .x12 .x0 (BitVec.ofNat 12 (32*n))
  | .output=>.ADDI .x12 .x22 (BitVec.ofNat 12 off)
def clearOps (n : Nat) : List Instr :=
  (List.range 4).map (fun k=>.SD .x0 .x0 (BitVec.ofNat 12 (32*n+8*k)))
def Act.ops (off : Nat) : Act → List Instr
  | .clear n=>clearOps n
  | .call src dst assign short=>[sourceOp src] ++ (if assign then [destOp off dst] else []) ++
      [.ECALL] ++ (if short then [.SH .x12 .x0 30] else [])
def Act.queries : Act → Nat | .clear _=>0 | .call ..=>1
def code (as_ : List Act) (off : Nat) := as_.flatMap (Act.ops off)
def queries (as_ : List Act) := (as_.map Act.queries).sum

structure Bank where
  cells : Nat→Term
  out : Option Term
  ptr : Option Dest
def replace (cells : Nat→Term) (n : Nat) (v : Term) := fun j=>if j=n then v else cells j
def Bank.put (b : Bank) (d : Dest) (v : Term) : Bank := match d with
  | .scratch n=>{cells:=replace b.cells n v,out:=b.out,ptr:=some d}
  | .output=>{cells:=b.cells,out:=some v,ptr:=some d}
def Bank.word (b : Bank) (src : Source) (short : Bool) := match src with
  | .leaf j=>Term.leaf j
  | .scratch n=>Term.hash short (b.cells n) (b.cells (n+1)) (b.cells (n+2))
def update (b : Bank) : Act → Bank
  | .clear n=>{b with cells:=replace b.cells n .zero}
  | .call src dst _ sh=>b.put dst (b.word src sh)

def scratchWrites (ls : List Act) := ls.filterMap fun
  | .clear n | .call _ (.scratch n) ..=>some n
  | _=>none
def initial (writes : List Nat) : Bank := ⟨fun n=>if n∈writes then .old n else .zero,none,none⟩
def allowed (limit : Nat) (writes : List Nat) (b : Bank) : Act → Bool
  | .clear n=>decide (n∈writes ∧ n<32)
  | .call src dst assign sh=>
    (match src with | .leaf j=>decide (j<limit) && !sh | .scratch n=>decide (n+2<32)) &&
    (match dst with | .output=>true | .scratch n=>decide (n∈writes ∧ n<32)) &&
    (assign || decide (b.ptr=some dst))
def legal (limit : Nat) (writes : List Nat) (b : Bank) : List Act → Bool
  | []=>true
  | a::xs=>allowed limit writes b a && legal limit writes (update b a) xs

def wanted (limit : Nat) : Nat → Nat → Term
  | 0,j=>if j<limit then .leaf j else .zero
  | h+1,j=>if (3*2^h)*j<limit then
      let ar:=if h=0 then 3 else 2
      .hash (h != 0) (wanted limit h (ar*j)) (wanted limit h (ar*j+1))
        (if h=0 then wanted limit h (ar*j+2) else .zero)
    else .zero

end CommitGolfCandidate.RungA.Kernel
