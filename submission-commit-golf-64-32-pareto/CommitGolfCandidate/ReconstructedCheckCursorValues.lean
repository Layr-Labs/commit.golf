import CommitGolfCandidate.ReconstructedCheckValues
import CommitGolfCandidate.ReconstructedOpeningCursor

namespace CommitGolfCandidate.Reconstruction.CheckCursorValues
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CheckValues

/-- Numbered symbolic addresses for a reader at bit cursor 64*q+r.
Regions one and two hold the bit and byte displacements of the current
word. Regions three and four address that word and the proof base. -/
structure Context (env : Env) where
  q : Nat
  room : q<2^40
  bitBase : env.base 1=BitVec.ofNat 64 (64*q)
  byteBase : env.base 2=BitVec.ofNat 64 (8*q)
  proofWord : env.base 3=env.base 2+env.base 4

def narrow (a : Loc) := decide (a.offset.toNat<2048)

def pointer (r n : Nat) := Term.ptr ⟨r,BitVec.ofNat 64 n⟩

def shiftTerm : Term→Term
  | .ptr a => if a.region=1 then .lit a.offset else .ptr a
  | .bin .bitXor (.ptr a) (.lit w) =>
    if a.region=1 then .lit (a.offset ^^^ w) else .bin .bitXor (.ptr a) (.lit w)
  | t=>t

private theorem offset_mod (env : Env) (ctx : Context env) (p : Loc) (r : p.region=1) :
    (physical env p).toNat%64=p.offset.toNat%64 := by
  simp only [physical,r,ctx.bitBase,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

private theorem xor_mod (x y : Word) : (x ^^^ y).toNat%64=x.toNat%64 ^^^ (y.toNat%64) := by
  rw [BitVec.toNat_xor]
  exact Nat.xor_mod_two_pow (a:=x.toNat) (b:=y.toNat) (n:=6)

theorem shift_sound (env : Env) (ctx : Context env) (t : Term) :
    ((shiftTerm t).val env).toNat%64=(t.val env).toNat%64 := by
  unfold shiftTerm;split
  · rename_i a;split
    · rename_i h;exact (offset_mod env ctx a h).symm
    · rfl
  · rename_i a w;split
    · rename_i h
      change (a.offset ^^^ w).toNat%64=(physical env a ^^^ w).toNat%64
      rw [xor_mod,xor_mod,offset_mod env ctx _ h]
    · rfl
  · rfl

def shifted (left : Bool) (x y : Term) : Term :=
  let kind:=if left then Bin.shl else Bin.shr
  match y with
  | .lit w=>if w.toNat%64=0 then x else applyOp kind x (.lit (BitVec.ofNat 64 (w.toNat%64)))
  | _=>applyOp kind x y

private theorem shift_value (env : Env) (left : Bool) (x y : Term) :
    (shifted left x y).val env=(if left then Bin.shl else Bin.shr).run (x.val env) (y.val env) := by
  have normalized (w : Word) : (BitVec.ofNat 64 (w.toNat%64)).toNat%64=w.toNat%64 := by
    simp only [BitVec.toNat_ofNat];omega
  cases left <;> cases y <;> simp only [shifted,ite_false,ite_true,Bool.false_eq_true,op_sound,Term.val,Bin.run]
  all_goals split <;> rename_i z <;> simp_all [op_sound,Term.val,Bin.run,normalized]

def apply (op : Bin) (x y : Term) : Term :=
  match op,x,y with
  | .add,.ptr a,.ptr b =>
    if a.region=2 ∧ b.region=4 then .ptr ⟨3,a.offset+b.offset⟩ else applyOp .add (.ptr a) (.ptr b)
  | .shr,.ptr a,.lit k =>
    if a.region=1 ∧ k=3 ∧ narrow a=true then pointer 2 (a.offset.toNat/8)
    else applyOp .shr (.ptr a) (.lit k)
  | .bitAnd,.ptr a,.lit mask =>
    if a.region=1 ∧ mask=63 then .lit (BitVec.ofNat 64 (a.offset.toNat%64))
    else if a.region=2 ∧ mask=signExtend12 4088 then pointer 2 (8*(a.offset.toNat/8))
    else applyOp .bitAnd (.ptr a) (.lit mask)
  | .shl,x,y=>shifted true x (shiftTerm y)
  | .shr,x,y=>shifted false x (shiftTerm y)
  | op,x,y=>applyOp op x y

private theorem pair (env : Env) (ctx : Context env) (a b : Loc) (r : a.region=2) (s : b.region=4) :
    physical env ⟨3,a.offset+b.offset⟩=physical env a+physical env b := by
  have commute (p q r : Word) : p+(q+r)=q+(p+r) := by rw [←BitVec.add_assoc,BitVec.add_comm p q,BitVec.add_assoc]
  simp [physical,r,s,ctx.proofWord,BitVec.add_assoc,commute,BitVec.add_comm]

private theorem shr3 (env : Env) (ctx : Context env) (a : Loc) (r : a.region=1) (fit : narrow a=true) :
    (pointer 2 (a.offset.toNat/8)).val env=physical env a >>> (3 : Nat) := by
  have h : a.offset.toNat<2048:=of_decide_eq_true fit
  have b:=ctx.room
  have offset : a.offset=BitVec.ofNat 64 a.offset.toNat:=by simp
  apply BitVec.eq_of_toNat_eq
  simp only [pointer,Term.val,physical,r,ctx.bitBase,ctx.byteBase,BitVec.toNat_ushiftRight,
    BitVec.toNat_add,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  omega

private theorem low6 (env : Env) (ctx : Context env) (a : Loc) (r : a.region=1) :
    BitVec.ofNat 64 (a.offset.toNat%64)=(physical env a &&& 63#64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_and]
  change _=(physical env a).toNat &&& (2^6-1)
  rw [Nat.and_two_pow_sub_one_eq_mod,offset_mod env ctx a r];omega

private theorem aligned (env : Env) (ctx : Context env) (a : Loc) (r : a.region=2) :
    (pointer 2 (8*(a.offset.toNat/8))).val env=physical env a &&& signExtend12 4088 := by
  have val : physical env a=BitVec.ofNat 64 (8*ctx.q+a.offset.toNat) := by
    simp [physical,r,ctx.byteBase,BitVec.ofNat_add]
  rw [val]
  change (env.base 2+BitVec.ofNat 64 (8*(a.offset.toNat/8)))=alignToDword (BitVec.ofNat 64 _)
  rw [ctx.byteBase,OpeningCursor.aligned,←BitVec.ofNat_add]
  congr 1;omega

theorem sound (env : Env) (ctx : Context env) (op : Bin) (x y : Term) :
    (apply op x y).val env=op.run (x.val env) (y.val env) := by
  unfold apply;split
  · rename_i a b;split
    · rename_i h;exact pair env ctx a b h.1 h.2
    · apply op_sound
  · rename_i a k;split
    · rename_i h;rw [h.2.1];exact shr3 env ctx a h.1 h.2.2
    · apply op_sound
  · rename_i a m;split
    · rename_i h;rw [h.2];exact low6 env ctx a h.1
    · split
      · rename_i h;rw [h.2];exact aligned env ctx a h.1
      · apply op_sound
  · rw [shift_value];change _ <<< _ = _ <<< _;rw [shift_sound env ctx]
  · rw [shift_value];change _ >>> _ = _ >>> _;rw [shift_sound env ctx]
  · apply op_sound

end CommitGolfCandidate.Reconstruction.CheckCursorValues
