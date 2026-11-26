import CommitGolfCandidate.R4bFieldFacts
import CommitGolfCandidate.R4bEmit
import CommitGolfCandidate.R4bGeometry
set_option Elab.async false
namespace CommitGolfCandidate.R4b
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open CommitGolfCandidate.S4
open Open (Sources offsetAt widthAt)
open Machine (W proofBase)

def temporary : Reg→Bool
  | .x6 | .x7 | .x8 | .x12 | .x14 | .x20 | .x21 | .x22 | .x28=>true
  | _=>false
def Kept (s t : MachineState) := ∀ r,temporary r=false → t.getReg r=s.getReg r
theorem Kept.trans {s t u : MachineState} (h : Kept s t) (k : Kept t u) : Kept s u :=
  fun r n=>(k r n).trans (h r n)
theorem Kept.fixed {s t : MachineState} {b : Nat} (h : Kept s t) (ag : Agree (R4b.fixed b) s) : Agree (R4b.fixed b) t := by
  intro r n e
  have no : temporary r=false:=by cases r <;> first | rfl | simp [R4b.fixed] at e
  exact (h r no).trans (ag _ _ e)
theorem protectMarks {s t : MachineState} {ps : Positions} {r : Nat} (h : Protect s t) (m : Open.Marked ps r s) : Open.Marked ps r t :=
  fun u b=>(h _ (by omega) (Or.inl (by unfold proofBase;omega))).trans (m u b)

private theorem addrWrites : ∀ l : Fin 4,∀ q : Fin 17,((addressOps l q).map Op.dest).all temporary := by decide
theorem joinedRegs {s : MachineState} {tile i q : Nat} (f : Agree (fixed tile) s) (l : Agree (locals i q) s) :
    Agree (env tile i q) s := by
  intro r n h
  cases e:locals i q r with
  | none=>exact f r n (by simpa [env,e] using h)
  | some val=>exact l r n (by simpa [env,e] using h)

theorem fieldRun (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (t l q : Nat)
    (bt : t<32) (bl : l<4) (bq : q<17) (s : MachineState) (src : Sources td ps s) (table : TableMem s)
    (consts : Agree (fixed t) s) (states : Agree (locals (recordIndex ps (4*t+l)).val q) s)
    (out : s.getReg .x19=W (proofBase+2040*t))
    (cur : Cursor (tape td ps) (510*(4*t+l)+offsetAt true q) s) :
    ∃ z,Straight s (fieldCode l q) z ∧ Protect s z ∧ Kept s z ∧
      Agree (locals (recordIndex ps (4*t+l)).val (q+1)) z ∧
      Cursor (tape td ps) (510*(4*t+l)+offsetAt true (q+1)) z := by
  let r:=4*t+l;let i:=recordIndex ps r
  have bi : i.val<16777216:=i.isLt
  obtain ⟨ok,addr,form⟩:=allFacts bq bt bl bi
  obtain ⟨u,prep,mem,regs,stable⟩:=runAddress s (addressOps l q) (reads r i.val) (env t i.val q)
    (joinedRegs consts states) ok (memoryReads r (by dsimp [r];omega) batch src table)
  have saved : Kept s u:=by
    intro k no;apply stable
    intro inside
    have af:=addrWrites ⟨l,bl⟩ ⟨q,bq⟩
    have yes:=List.all_eq_true.mp af k inside
    rw [no] at yes;contradiction
  have noCarry : .x20∉(addressOps l q).map Op.dest := by
    exact (show ∀ a : Fin 4,∀ b : Fin 17,Reg.x20∉(addressOps a b).map Op.dest by decide) ⟨l,bl⟩ ⟨q,bq⟩
  have address := (regs .x12 _ addr).trans (congrArg W (sourceEq i q bq))
  obtain ⟨z,copy,away,scratch,next⟩:=emit td ps batch t l q bt bl bq u ((Protect.ofMem mem).sources src) address
    ((saved _ rfl).trans out) (cur.mem mem (stable _ noCarry))
  have kept : Kept u z:=by
    intro k no;apply scratch <;> intro e <;> subst k <;> contradiction
  refine ⟨z,prep.append copy,(Protect.ofMem mem).trans away,saved.trans kept,?_,?_⟩
  · intro k n h
    have non : k≠.x6 ∧ k≠.x7 ∧ k≠.x20:=by
      cases k <;> first | decide | simp [locals] at h
    exact (scratch k non.1 non.2.1 non.2.2).trans (regs k n (form k n h))
  · simpa only [Nat.add_assoc,(offsetMore q bq).1] using next

theorem fieldsRun (td : Late.Trapdoor) (ps : Positions) (batch : ps.card=128) (t l : Nat)
    (bt : t<32) (bl : l<4) (s : MachineState) (src : Sources td ps s) (table : TableMem s)
    (consts : Agree (fixed t) s) (out : s.getReg .x19=W (proofBase+2040*t))
    (cur : Cursor (tape td ps) (510*(4*t+l)) s) (q : Nat) (bound : q≤17) :
    ∃ z,Straight s ((List.range q).flatMap (fieldCode l)) z ∧ Protect s z ∧ Kept s z ∧
      Agree (locals (recordIndex ps (4*t+l)).val q) z ∧
      Cursor (tape td ps) (510*(4*t+l)+offsetAt true q) z := by
  induction q with
  | zero=>
    refine ⟨s,.nil _,Protect.ofMem rfl,fun _ _=>rfl,?_,cur⟩
    intro r n h;cases r <;> simp [locals] at h
  | succ q ih=>
    obtain ⟨u,pre,frame,keep,dyn,ptr⟩:=ih (by omega)
    obtain ⟨z,last,away,stable,ag,next⟩:=fieldRun td ps batch t l q bt bl (by omega) u (frame.sources src)
      (frame.table table) (keep.fixed consts) dyn ((keep _ rfl).trans out) ptr
    rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    exact ⟨z,pre.append last,frame.trans away,keep.trans stable,ag,next⟩
end CommitGolfCandidate.R4b
