import CommitGolfCandidate.S4FieldAccess
import CommitGolfCandidate.S4RawProof
import CommitGolfCandidate.S4Address

set_option Elab.async false
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (Fragment W)
open Machine.Sym (Calc Expr original mkOp)
def slotOps (l : Nat) : List Calc :=
  [.lbu .x7 .x24 (BitVec.ofNat 12 (2*l)),.lbu .x30 .x24 (BitVec.ofNat 12 (2*l+1)),.bor .x30 .x7 .x30,
   .addi .x30 .x30 4095,.addi .x21 .x22 (BitVec.ofNat 12 (96*l)),.slli .x7 .x7 5,.add .x21 .x21 .x7,
   .addi .x12 .x23 (BitVec.ofNat 12 (96*(l/2)+32*(l%2))),.bxor .x12 .x12 .x21,.band .x12 .x12 .x30,.bxor .x12 .x12 .x21]
def slotMoves (l : Nat) : Machine.Burst:=⟨.x12,.x19,0,0,pieces (30*l) 30⟩
def slotPC (tail : Bool) : Nat→Nat
  | 0=>if tail then 5177 else 4903
  | l+1=>slotPC tail l+11+2*(slotMoves l).widths.length+1
def slotPrice (l : Nat) := 11+2*(slotMoves l).widths.length+1
def slotWords (tail : Bool) (l : Nat) :=
  let pc:=slotPC tail l
  let bump:=pc+11+2*(slotMoves l).widths.length
  (Fragment.arithmetic (slotOps l)).valid .opening pc (pc+11) &&
    (Fragment.copy (slotMoves l)).valid .opening (pc+11) bump &&
    Machine.stands .opening bump (.ADDI .x19 .x19 30)
set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
theorem slotSite : ∀ tail : Bool,∀ l : Fin 8,(tail=false ∨ l.val<3) → slotWords tail l := by decide

def flagExpr (j : Nat) := Expr.byteLoad (plus (.reg .x24) (lit j))
def slotExpression (l : Nat) : Expr :=
  let flagL:=flagExpr (2*l);let flagR:=flagExpr (2*l+1)
  let mask:=plus (mkOp .bor flagL flagR) (lit (2^64-1))
  let peer:=plus (plus (.reg .x22) (lit (96*l))) (sh flagL 5)
  let parent:=plus (.reg .x23) (lit (96*(l/2)+32*(l%2)))
  mkOp .xor (mkOp .and (mkOp .xor parent peer) mask) peer
def readAddresses (l : Nat) : List (Expr×Nat) :=
  [(plus (.reg .x24) (lit (2*l)),1),(plus (.reg .x24) (lit (2*l+1)),1)]
set_option maxRecDepth 5000 in
theorem slotForm : ∀ l : Fin 8,
  ((slotOps l).foldl Machine.Sym.bump original) .x12=slotExpression l ∧
  Machine.Sym.requirements original (slotOps l)=readAddresses l ∧
  (slotOps l).all (fun c=>[Reg.x6,.x7,.x12,.x21,.x30].contains c.dst) ∧
  (slotOps l).all (fun c=>c.dst != .x0) ∧ Machine.bytesOf (slotMoves l).widths=30 ∧
  safeLayout (30*l.val) 30 0 (slotMoves l).widths := by decide

def flagWord (b : Bool) : Word:=if b then 1 else 0
def slotSource (left right : Bool) (j : Nat) := if left then Late.nodeAddress 15 (2*j+1)
  else if right then Late.nodeAddress 15 (2*j) else Late.nodeAddress 16 j

theorem slotGeometry : ∀ t : Fin 22,∀ l : Fin 8,8*t.val+l.val<171 →
  Late.rowAddress 15 (8*t.val)+96*l.val=Late.nodeAddress 15 (2*(8*t.val+l.val)) ∧
  Late.rowAddress 15 (8*t.val)+96*l.val+32=Late.nodeAddress 15 (2*(8*t.val+l.val)+1) ∧
  Late.nodeAddress 16 (8*t.val)+(96*(l.val/2)+32*(l.val%2))=Late.nodeAddress 16 (8*t.val+l.val) := by decide

private theorem chooseWord (left right : Bool) (x y : Word) :
    ((y ^^^ x) &&& ((flagWord left ||| flagWord right)+W (2^64-1))) ^^^ x=if left || right then x else y := by
  rw [BitVec.xor_comm ((y ^^^ x) &&& _) x,BitVec.xor_comm y x]
  rw [show W (2^64-1)=(-1 : Word) by decide,←BitVec.sub_eq_add_neg]
  exact Machine.slotPick left right x y

attribute [local irreducible] Late.nodeAddress Late.rowAddress
set_option maxRecDepth 4000 in
theorem slotAddressValue (t : Fin 22) (l : Fin 8) (inside : 8*t.val+l.val<171) (s : MachineState) (left right : Bool)
    (a : (flagExpr (2*l.val)).eval s=flagWord left) (b : (flagExpr (2*l.val+1)).eval s=flagWord right)
    (kids : s.getReg .x22=W (Late.rowAddress 15 (8*t.val)))
    (cap : s.getReg .x23=W (Late.nodeAddress 16 (8*t.val))) :
    (slotExpression l).eval s=W (slotSource left right (8*t.val+l.val)) := by
  obtain ⟨even,odd,parent⟩:=slotGeometry t l inside
  let j:=8*t.val+l.val
  have c : s.getReg .x23+W (96*(l.val/2)+32*(l.val%2))=W (Late.nodeAddress 16 j):=by
    rw [cap];exact (BitVec.ofNat_add ..).symm.trans (congrArg W parent)
  let peer:=if left then Late.nodeAddress 15 (2*j+1) else Late.nodeAddress 15 (2*j)
  have k : s.getReg .x22+W (96*l.val)+(flagWord left <<< 5)=W peer:=by
    rw [kids]
    cases left
    · change W _+W _+(0 : Word)=_
      exact (BitVec.add_zero _).trans ((BitVec.ofNat_add ..).symm.trans (congrArg W even))
    · change W _+W _+W 32=_
      rw [←BitVec.ofNat_add,←BitVec.ofNat_add];exact congrArg W odd
  simp only [slotExpression,Machine.Sym.eval_mkOp,Machine.Sym.Expr.eval,Machine.Sym.Bin.apply,plus,sh,lit,a,b,c,
    show (W 5).toNat=5 by decide,k]
  apply (chooseWord left right (W peer) (W (Late.nodeAddress 16 j))).trans
  cases left <;> cases right <;> rfl
end CommitGolfCandidate.S4.Open
