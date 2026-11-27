import CommitGolfCandidate.S4FieldExpr

set_option Elab.async false
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Machine (W Width validOffsets)
open Machine.Sym (Expr original requirements)

def safeLayout (off len : Nat) : Nat→List Width→Bool
  | _,[]=>true
  | j,w::ws=>decide (j+w.size≤len ∧ 8%w.size=0 ∧ j%w.size=0 ∧ (off+j)%w.size=0 ∧
                  signExtend12 (BitVec.ofNat 12 j)=W j) && safeLayout off len (j+w.size) ws

theorem safeActual (off src dst len j : Nat) (ws : List Width) (ok : safeLayout off len j ws)
    (a : src%8=0) (b : dst%8=off%8) (sb : src+len≤MEMORY_BYTES) (db : dst+len≤MEMORY_BYTES) :
    validOffsets src dst j j ws := by
  induction ws generalizing j with
  | nil=>trivial
  | cons w ws ih=>
    obtain ⟨vals,rest⟩:=Bool.and_eq_true_iff.mp ok
    obtain ⟨limit,_,sx,dx,imm⟩:=of_decide_eq_true vals
    have start : (src+j)%w.size=0∧(dst+j)%w.size=0:=by
      cases w <;> simp only [Width.size] at sx dx ⊢ <;> omega
    exact ⟨⟨by omega,start.1⟩,⟨by omega,start.2⟩,imm,imm,ih _ rest⟩

set_option maxRecDepth 5000 in
private theorem verified : ∀ b : Bool,∀ l : Fin 8,∀ q : Fin 26,q.val<fieldsIn b →
    safeLayout (recordBytes b*l+offsetAt b q) (widthAt b q) 0 (moves b l q).widths ∧
    (prepare b l q).all (fun c=>c.dst != .x0)=true ∧
    signExtend12 (BitVec.ofNat 12 (widthAt b q))=W (widthAt b q) := by decide

theorem fieldSafe (b : Bool) (l q src dst : Nat) (bl : l<8) (bq : q<fieldsIn b) (a : src%8=0)
    (d : dst%8=(recordBytes b*l+offsetAt b q)%8)
    (sb : src+widthAt b q≤MEMORY_BYTES) (db : dst+widthAt b q≤MEMORY_BYTES) :
    validOffsets src dst 0 0 (moves b l q).widths ∧ (∀ c∈prepare b l q,c.dst≠.x0) ∧
    signExtend12 (BitVec.ofNat 12 (widthAt b q))=W (widthAt b q) := by
  have lim : q<26:=by unfold fieldsIn at bq;split at bq <;> omega
  obtain ⟨layout,nz,imm⟩:=verified b ⟨l,bl⟩ ⟨q,lim⟩ bq
  exact ⟨safeActual _ _ _ _ _ _ layout a d sb db,fun c h=>bne_iff_ne.mp (List.all_eq_true.mp nz c h),imm⟩

private theorem indexReads : ∀ b : Bool,∀ l : Fin 8,requirements original (prepare b l 0)=
    [(plus (.reg (ixReg b)) (lit (8*l.val)),8)] := by decide
private theorem remainingReads : ∀ b : Bool,∀ q : Fin 26,0<q.val → q.val<fieldsIn b →
    requirements original (prepare b 0 q)=[] := by decide

theorem prefixReads (b : Bool) (l q : Nat) (bl : l<8) (bq : q<fieldsIn b) (s : MachineState)
    (initial : q=0 → accessValid (s.getReg (ixReg b)+W (8*l)) 8=true) :
    ∀ a∈requirements original (prepare b l q),accessValid (a.1.eval s) a.2=true := by
  by_cases z : q=0
  · subst q;rw [show requirements original (prepare b l 0)=_ from indexReads b ⟨l,bl⟩]
    intro a ha;rcases List.mem_singleton.mp ha with rfl
    simpa only [plus,lit,Machine.Sym.eval_mkOp,Expr.eval,Machine.Sym.Bin.apply] using initial rfl
  · have lim : q<26:=by unfold fieldsIn at bq;split at bq <;> omega
    have e:=remainingReads b ⟨q,lim⟩ (Nat.pos_of_ne_zero z) bq
    simp only [prepare,if_neg z] at e ⊢;rw [e];intro a ha;cases ha
end CommitGolfCandidate.S4.Open
