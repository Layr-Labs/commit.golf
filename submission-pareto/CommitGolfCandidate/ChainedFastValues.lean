import CommitGolfCandidate.ChainedFastView
namespace CommitGolfCandidate.Chained.Native.Fast
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 520

def childExpr (h : Low) (i : Fin 8) : Expr :=
  if i.val=3 ∨ i.val=7 then .band (.cell (cslot i)) (.reg .x3) else .cell (cslot i)
def firstExpr (h : Low) (i : Fin 8) : Expr :=
  let x:=childExpr h
  match i.val with
  | 0=>x 0 | 1=>x 1 | 2=>x 2 | 3=>.bor (.shl (x 4) 46) (x 3)
  | 4=>.bor (.shr (x 4) 18) (.shl (x 5) 46)
  | 5=>.bor (.shr (x 5) 18) (.shl (x 6) 46)
  | 6=>.bor (.shr (x 6) 18) (.shl (x 7) 46)
  | _=>.bor (.shr (x 7) 18) (.reg .x16)
def tagReg (j : Nat) := if j=0 then Reg.x17 else if j=1 then .x18 else .x19
def inputAt (h : Low) (j : Fin 4) (i : Fin 8) : Expr :=
  if j.val=0 then firstExpr h i
  else if a : i.val<4 then .reply (j.val-1) ⟨i.val,a⟩
  else if i.val=4 then .reg (tagReg (j.val-1)) else .cell (srcSlot false i)
def outputExpr (h : Low) (i : Slot) : Expr :=
  if ch:i.val<8 then childExpr h ⟨i.val,ch⟩
  else if own:i.val<12 then
    let term:=Expr.reply 3 ⟨i.val-8,by omega⟩
    if h.val=7 ∧ i.val=11 then .band term (.reg .x15) else term
  else if buf:i.val<16 then .reply 2 ⟨i.val-12,by omega⟩
  else if i.val=16 then .reg .x19 else .cell i
private def req (h : Low) (j : Fin 4) :=
  (requests initial (plan h)).getD j.val (0,fun _=>.reg .x0)
private theorem request_count (h : Low) : (requests initial (plan h)).length=4 := by fin_cases h <;> rfl
private theorem request_row : ∀ h : Low, ∀ j : Fin 4, (req h j).1=j.val ∧
    ∀ i : Fin 8, (req h j).2 i=inputAt h j i := by decide +kernel
private theorem outputs : ∀ h : Low, ∀ i : Slot, ((plan h).foldl update initial).m i=outputExpr h i := by decide +kernel

def CanonicalWords (s : MachineState) (n : Nat) (h : Low) (left right : BitVec 238) :=
  ∀ i : Fin 8, interp s n (fun _=>0) (childExpr h i) =
    if i.val<4 then childWord left i.val else childWord right (i.val-4)

private theorem child_bank (s : MachineState) (n : Nat) (h : Low) (ys : Nat→Output) (i : Fin 8) :
    interp s n ys (childExpr h i)=interp s n (fun _=>0) (childExpr h i) := by
  unfold childExpr;split <;>rfl

structure Tags (s : MachineState) (h : Low) : Prop where
  heightReg : s.getReg .x16=W h.val <<< 28
  c0 : s.getReg .x17=W (7*h.val)
  c1 : s.getReg .x18=W (7*h.val+1)
  c2 : s.getReg .x19=W (7*h.val+2)
  zero0 : s.getMem 264=0
  zero1 : s.getMem 272=0
  flag : s.getMem 280=(2^63:Word)

theorem first_value (n : Nat) (s : MachineState) (h : Low) (ys : Nat→Output)
    (left right : BitVec 238) (x:CanonicalWords s n h left right) (t:Tags s h) :
    cat8 (fun i=>interp s n ys (inputAt h 0 i))=canonicalEncoding.first (height h) (right ++ left) := by
  rw [←first_packed_encoding]
  have v (i : Fin 8) := (child_bank s n h ys i).trans (x i)
  have each (i : Fin 8) : interp s n ys (inputAt h 0 i)=firstPackedWord (W h.val) left right i.val := by
    fin_cases i <;> simp only [inputAt,firstExpr,Fin.val_zero,Fin.val_mk,Fin.isValue,ite_true,
      firstPackedWord,interp,v,t.heightReg,BitVec.or_comm] <;> rfl
  simp only [cat8,each,firstPackedValue,height,BitVec.append_assoc,BitVec.cast_eq]
  rfl

private theorem cat4 (x : Output) :
    ew x 3 ++ ew x 2 ++ ew x 1 ++ ew x 0=x := by
  change x.extractLsb' 192 64 ++ x.extractLsb' 128 64 ++ x.extractLsb' 64 64 ++ x.extractLsb' 0 64=x
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 192=128+64),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128=64+64),
    BitVec.extractLsb'_append_extractLsb' (w:=192) (len:=64)]

private theorem append_val {a b : Nat} (high : BitVec a) (low : BitVec b) :
    (high ++ low).toNat=high.toNat*2^b+low.toNat := by
  rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt low.isLt,Nat.shiftLeft_eq]

theorem next_value (n : Nat) (s : MachineState) (h : Low) (ys : Nat→Output) (j : Fin 3) (t:Tags s h) :
    cat8 (fun i=>interp s n ys (inputAt h ⟨j.val+1,by omega⟩ i)) =
    canonicalEncoding.next (height h) (j.val+1) (ys j.val) := by
  have tag : s.getReg (tagReg j.val)=W (7*h.val+j.val) := by
    fin_cases j <;> simp [tagReg,t.c0,t.c1,t.c2]
  change _=encodeNext _ _ _
  rw [encodeNext_valid _ _ _ (by omega) (by have:=j.isLt;omega)]
  have high : cat8 (fun i=>interp s n ys (inputAt h ⟨j.val+1,by omega⟩ i)) =
      (((2^63:Word) ++ (0:Word) ++ (0:Word) ++ W (7*h.val+j.val)) ++ ys j.val) := by
    unfold cat8
    have m0 : s.getMem (W 264)=0:=t.zero0
    have m1 : s.getMem (W 272)=0:=t.zero1
    have m2 : s.getMem (W 280)=2^63:=t.flag
    simp [inputAt,interp,srcSlot,address,tag,m0,m1,m2,cat4]
  rw [high]
  apply BitVec.eq_of_toNat_eq
  rw [pack_value]
  have tagSmall : 7*h.val+j.val<2^64 := by have:=h.isLt;have:=j.isLt;omega
  simp only [append_val, W,BitVec.toNat_ofNat,symbolCode,height,Nat.add_sub_cancel]
  rw [Nat.mod_eq_of_lt tagSmall]
  change (((2^63*2^64+0)*2^64+0)*2^64+(7*h.val+j.val))*2^256+(ys j.val).toNat=_
  ring

noncomputable def replies (o : Oracle) (h : Low) (left right : BitVec 238) : Nat→Output
  | 0=>o.compression (canonicalEncoding.first (height h) (right++left))
  | j+1=>o.compression (canonicalEncoding.next (height h) (j+1) (replies o h left right j))

theorem node_matches (o : Oracle) (h : Low) (s : MachineState) (n : Nat) (bn : Bounds n)
    (left right : BitVec 238) (words : CanonicalWords s n h left right) (tg:Tags s h) :
    Matches s n (replies o h left right) ((plan h).foldl update initial) (checkEvaluation o (trace n (plan h) s)).1 := by
  apply simulate o bn _ _ _ (initial_matches ..)
  intro item member
  obtain ⟨j,lt,eq⟩:=List.getElem_of_mem member
  have hx : j<4 := by rwa [request_count] at lt
  let i : Fin 4 := ⟨j,hx⟩
  have same : req h i=item := by unfold req;rw [List.getD_eq_getElem _ _ lt,eq]
  rw [←same]
  change o.compression (cat8 (fun k=>interp s n (replies o h left right) ((req h i).2 k))) = replies o h left right (req h i).1
  simp only [(request_row h i).1,(request_row h i).2]
  have all (idx : Fin 4) : o.compression (cat8 (fun k=>interp s n (replies o h left right) (inputAt h idx k))) =
      replies o h left right idx.val := by
    obtain ⟨idx,lt⟩:=idx
    cases idx with
    | zero => exact congrArg o.compression (first_value n s h _ left right words tg)
    | succ p => exact congrArg o.compression (next_value n s h _ ⟨p,by omega⟩ tg)
  exact all i

theorem node_memory (o : Oracle) (h : Low) (s : MachineState) (n : Nat) (bn : Bounds n)
    (left right : BitVec 238) (words : CanonicalWords s n h left right) (tg:Tags s h) (i : Slot) :
    (checkEvaluation o (trace n (plan h) s)).1.getMem (W (address n i)) =
      interp s n (replies o h left right) (outputExpr h i) :=
  ((node_matches o h s n bn left right words tg).mem i).trans (congrArg _ (outputs h i))

end CommitGolfCandidate.Chained.Native.Fast
