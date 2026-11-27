import CommitGolfCandidate.S4CarryState
import CommitGolfCandidate.S4Catalog
import CommitGolfCandidate.S4Kernel

set_option Elab.async false
namespace CommitGolfCandidate.S4.Codec
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Carry (group carrier pieces prev delta)
def program (d : Bool) : Code := if d then .check else .opening
def entry (d : Bool) := if d then 12988 else 5876
def firstOps (d : Bool) : List Sym.Calc := [if d then .addi .x21 .x18 0 else .sub .x21 .x19 .x11,
  .addi .x22 .x0 34,.slli .x22 .x22 11,.addi .x22 .x22 448,.add .x22 .x21 .x22]
def bytePC (d : Bool) (k : Nat) := entry d+5+(if d then 7*group k 0+k else 8*group k 0)
def beginByte (d : Bool) (k : Nat) : Sym.Calc := if d then .addi .x8 .x0 0 else .lbu .x7 .x22 (BitVec.ofNat 12 k)
def piecePC (d : Bool) (k p : Nat) := bytePC d k+1+(if d then 7*p-(if p=0 then 0 else 1) else 8*p)
def before (d : Bool) (c : Nat) : List Sym.Calc :=
  [.addi .x21 .x21 (BitVec.ofNat 12 (delta c)),.lbu .x6 .x21 0]++
  (if d then [.srli .x7 .x6 6,.andi .x6 .x6 63] else
    [.andi .x8 .x7 3,.slli .x8 .x8 6,.andi .x6 .x6 63,.bor .x6 .x6 .x8])
def after (d more : Bool) (p : Nat) : List Sym.Calc :=
  if d then (if p=0 then [] else [.slli .x7 .x7 (BitVec.ofNat 6 (2*p))])++[.bor .x8 .x8 .x7]
  else if more then [.srli .x7 .x7 2] else []
def prefixOps (d : Bool) (k p : Nat) := before d (group k p)
def suffixOps (d : Bool) (k p : Nat) := after d (decide (p+1<pieces k)) p
def sequence (d : Bool) (k p : Nat) := (prefixOps d k p).map Sym.Calc.instr++
    [.SB .x21 .x6 0]++(suffixOps d k p).map Sym.Calc.instr
def endByte (k : Nat) : Instr := .SB .x22 .x8 (BitVec.ofNat 12 k)
def donePC (d : Bool) := bytePC d 330
def nextPiece (d : Bool) (k p : Nat) :=
  if p+1<pieces k then piecePC d k (p+1) else bytePC d (k+1)-(if d then 1 else 0)
set_option maxRecDepth 12000
private theorem prices : ∀ d : Bool,∀ k : Fin 330,∀ p : Fin 4,p.val<pieces k →
    piecePC d k p+(sequence d k p).length=nextPiece d k p ∧
    piecePC d k p+(sequence d k p).length≤(program d).count := by decide
theorem price (d : Bool) (k p : Nat) (hk : k<330) (hp : p<pieces k) :
    piecePC d k p+(sequence d k p).length=nextPiece d k p ∧
    piecePC d k p+(sequence d k p).length≤(program d).count := by
  have four : p<4:=by unfold pieces at hp;split at hp <;> omega
  exact prices d ⟨k,hk⟩ ⟨p,four⟩ hp
end CommitGolfCandidate.S4.Codec
