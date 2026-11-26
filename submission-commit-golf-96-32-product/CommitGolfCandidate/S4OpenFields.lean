import CommitGolfCandidate.S4Catalog
import CommitGolfCandidate.S4Geometry
import CommitGolfCandidate.LateLayout
import CommitGolfCandidate.S4Wire
namespace CommitGolfCandidate.S4.Open
open CommitGolf RiscvZkvm.Rv64
open Machine (W Width Burst Fragment)
open Machine.Sym (Calc)
def rowReg (batch : Bool) := if batch then Reg.x21 else .x22
def ixReg (batch : Bool) := if batch then Reg.x13 else .x21
def widthAt (batch : Bool) (q : Nat) := if q=0 then 24 else fieldBytes batch (q-2)
def offsetAt (batch : Bool) (q : Nat) := if q=0 then 0 else fieldOffset batch (q-2)+(if q=2 then 32 else 0)
def fieldsIn (b : Bool) := if b then 17 else 26

def immediate3 (r : Reg) (n : Nat) : List Calc :=
  [.addi r .x0 (BitVec.ofNat 12 (n/2^22%2048)),.slli r r 11,.addi r r (BitVec.ofNat 12 (n/2048%2048)),
   .slli r r 11,.addi r r (BitVec.ofNat 12 (n%2048))]

def saltPrep (batch : Bool) (lane : Nat) : List Calc :=
  [.ld .x8 (ixReg batch) (BitVec.ofNat 12 (8*lane))] ++ immediate3 .x12 (Late.rowBase+72) ++
  [.srli .x6 .x8 1,.addi .x7 .x0 184,.mul .x6 .x6 .x7,.add .x12 .x12 .x6,.andi .x6 .x8 1,
   .slli .x6 .x6 4,.add .x12 .x12 .x6,.addi .x6 .x6 0]

def rotation : List Calc := [.addi .x7 .x7 1,.remu .x7 .x7 .x27]
def siblingPrep (batch : Bool) (q : Nat) : List Calc :=
  let row:=rowReg batch
  let address : List Calc:=[.slli .x6 .x7 5,.add .x12 row .x6]
  if q=2 then rotation++address else
    (if q=1 then [.remu .x7 .x8 .x27,.divu .x8 .x8 .x27] else
          [.andi .x7 .x8 1,.srli .x8 .x8 1,.xori .x7 .x7 1]) ++
    [.slli row .x8 1,.add row row .x8,.slli row row 5] ++
    immediate3 .x6 (4294971424+Late.levelOffset (q-2)) ++ [.add row row .x6] ++
    (if q=1 then rotation else []) ++address

def prepare (batch : Bool) (lane q : Nat) := if q=0 then saltPrep batch lane else siblingPrep batch q

def pieces (base len : Nat) : List Width :=
  if base%8=0 then List.replicate (len/8) .dword++List.replicate (len%8/4) .word++List.replicate (len%4/2) .half
  else if base%4=0 then List.replicate (len/4) .word++List.replicate (len%4/2) .half
  else List.replicate (len/2) .half

def moves (batch : Bool) (lane q : Nat) : Burst :=
  ⟨.x12,.x19,0,0,pieces (recordBytes batch*lane+offsetAt batch q) (widthAt batch q)⟩
def advance (batch : Bool) (q : Nat) := Instr.ADDI .x19 .x19 (BitVec.ofNat 12 (widthAt batch q))
-- Each field has one arithmetic prefix, a sequence of exact-width transfers and one pointer increment.
def fieldSize (b : Bool) (l q : Nat) := (prepare b l q).length+2*(moves b l q).widths.length+1
def fieldCost (b : Bool) (l q : Nat) := Machine.Sym.price (prepare b l q)+2*(moves b l q).widths.length+1

theorem offsetSchedule : ∀ b : Bool,∀ q : Fin 26,q.val<fieldsIn b →
    offsetAt b q.val+widthAt b q.val=(if q.val+1<fieldsIn b then offsetAt b (q.val+1) else recordBytes b) := by decide
theorem movesSize : ∀ b : Bool,∀ l : Fin 8,∀ q : Fin 26,q.val<fieldsIn b →
    Machine.bytesOf (moves b l q).widths=widthAt b q := by decide
end CommitGolfCandidate.S4.Open
