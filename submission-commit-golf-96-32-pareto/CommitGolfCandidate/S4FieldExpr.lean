import CommitGolfCandidate.S4OpenFields

set_option Elab.async false
namespace CommitGolfCandidate.S4.Open
open CommitGolf RiscvZkvm.Rv64
open Machine (W)
open Machine.Sym (Expr mkOp bump original)
def lit (n : Nat) : Expr:=.lit (W n)
def plus := mkOp .add
def sh (e : Expr) (n : Nat) := mkOp .shl e (lit n)
def masked (e : Expr) (n : Nat) := mkOp .and e (lit n)
def scale96 (e : Expr) := sh (plus (sh e 1) e) 5
def fieldIndexExpr (b : Bool) (l q : Nat) : Expr :=
  if q=0 then .load (plus (.reg (ixReg b)) (lit (8*l)))
  else if q=1 then mkOp .divu (.reg .x8) (.reg .x27)
  else if q=2 then .reg .x8 else mkOp .shr (.reg .x8) (lit 1)

def laneExpr (q : Nat) : Expr :=
  if q=1 then mkOp .remu (plus (mkOp .remu (.reg .x8) (.reg .x27)) (lit 1)) (.reg .x27)
  else if q=2 then mkOp .remu (plus (.reg .x7) (lit 1)) (.reg .x27)
  else mkOp .xor (masked (.reg .x8) 1) (lit 1)

def rowExpr (b : Bool) (l q : Nat) : Expr :=
  if q=2 then .reg (rowReg b) else plus (scale96 (fieldIndexExpr b l q)) (lit (4294971424+Late.levelOffset (q-2)))

def fieldAddressExpr (b : Bool) (l q : Nat) : Expr :=
  if q=0 then
    let i:=fieldIndexExpr b l q
    plus (plus (lit (Late.rowBase+72)) (mkOp .mul (mkOp .shr i (lit 1)) (lit 184))) (sh (masked i 1) 4)
  else plus (rowExpr b l q) (sh (laneExpr q) 5)

def expectedRegs (b : Bool) (l q : Nat) : Prop :=
  let m:=(prepare b l q).foldl bump original
  m .x8=fieldIndexExpr b l q ∧ m .x12=fieldAddressExpr b l q ∧
    (q=1 → m .x7=laneExpr q ∧ m (rowReg b)=rowExpr b l q) ∧
    (prepare b l q).all (fun x=>[Reg.x6,.x7,.x8,.x12,rowReg b].contains x.dst)=true
instance (b : Bool) (l q : Nat) : Decidable (expectedRegs b l q) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private theorem heads : ∀ b : Bool,∀ l : Fin 8,expectedRegs b l 0 := by decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
private theorem rest : ∀ b : Bool,∀ q : Fin 26,0<q.val → q.val<fieldsIn b → expectedRegs b 0 q := by decide

theorem registerForm (b : Bool) (l q : Nat) (bl : l<8) (bq : q<fieldsIn b) : expectedRegs b l q := by
  by_cases z : q=0
  · subst q;exact heads b ⟨l,bl⟩
  · have lim : q<26:=by unfold fieldsIn at bq;split at bq <;> omega
    have e:=rest b ⟨q,lim⟩ (Nat.pos_of_ne_zero z) bq
    simpa only [expectedRegs,prepare,fieldIndexExpr,fieldAddressExpr,rowExpr,if_neg z] using e

theorem preserved (ops : List Machine.Sym.Calc) (r : Reg) (f : Reg→Expr)
    (untouched : ∀ c∈ops,c.dst≠r) : (ops.foldl bump f) r=f r := by
  induction ops generalizing f with
  | nil=>rfl
  | cons c cs ih=>
    rw [List.foldl_cons,ih (bump f c) (fun a b=>untouched a (List.mem_cons_of_mem _ b))]
    exact if_neg (untouched c (List.mem_cons_self ..))
end CommitGolfCandidate.S4.Open
