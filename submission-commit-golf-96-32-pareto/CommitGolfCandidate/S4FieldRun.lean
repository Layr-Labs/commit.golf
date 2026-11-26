import CommitGolfCandidate.S4FieldAccess
import CommitGolfCandidate.S4FieldPC
import CommitGolfCandidate.S4FieldMath
namespace CommitGolfCandidate.S4.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt pc_succ)
open Machine (W Width Moved Runs)
open Machine.Sym (Expr original bump)

def afterField (b : Bool) (l q : Nat) (s : MachineState) :=
  let t:=Machine.Sym.evaluated (prepare b l q) s
  let u:=Machine.copyBlock .x12 .x19 0 0 (moves b l q).widths t
  execInstrBr u (advance b q)
abbrev saved (b : Bool) (r : Reg) : Prop := r∉[Reg.x6,.x7,.x8,.x12,.x19,rowReg b]

structure FieldEnd (b : Bool) (l q dest : Nat) (i : Index) (s t : MachineState) : Prop where
  runs : Runs .opening s t (fieldSize b l q) (fieldCost b l q)
  pc : t.pc=pcAt (fieldPC b l (q+1))
  cursor : t.getReg .x19=W (dest+widthAt b q)
  node : t.getReg .x8=W (nodeIndex i.val (atLevel q))
  first : q=1 → t.getReg .x7=W (targetLane i q) ∧ t.getReg (rowReg b)=W (Late.rowAddress (q-2) (nodeIndex i.val ((q-2)+1)))
  keep : ∀ r,saved b r → t.getReg r=s.getReg r
  copied : Moved s t (targetAddr i q) dest (widthAt b q)

theorem runField (b : Bool) (l q dest : Nat) (i : Index) (s : MachineState)
    (bl : l<8) (bq : q<fieldsIn b) (which : b=true ∨ l=0) (valid : fieldValid b l q)
    (pc : s.pc=pcAt (fieldPC b l q)) (state : FieldState b l q i s) (ptr : s.getReg .x19=W dest)
    (ixSafe : q=0 → accessValid (s.getReg (ixReg b)+W (8*l)) 8=true)
    (aligned : targetAddr i q%8=0) (residue : dest%8=(recordBytes b*l+offsetAt b q)%8)
    (sb : targetAddr i q+widthAt b q≤MEMORY_BYTES) (db : dest+widthAt b q≤MEMORY_BYTES)
    (disjoint : targetAddr i q+widthAt b q≤dest) :
    FieldEnd b l q dest i s (afterField b l q s) := by
  let ops:=prepare b l q
  let p:=moves b l q
  let t:=Machine.Sym.evaluated ops s
  let u:=Machine.copyBlock .x12 .x19 0 0 p.widths t
  have lim : q<26:=by unfold fieldsIn at bq;split at bq <;> omega
  have endSmall:=fieldLimit b ⟨l,bl⟩ ⟨q,lim⟩ bq which
  have length : Machine.bytesOf p.widths=widthAt b q:=movesSize b ⟨l,bl⟩ ⟨q,lim⟩ bq
  obtain ⟨pair,inc⟩:=Bool.and_eq_true_iff.mp valid
  obtain ⟨arithmetic,copy⟩:=Bool.and_eq_true_iff.mp pair
  obtain ⟨safe,nz,imm⟩:=fieldSafe b l q _ _ bl bq aligned residue sb db
  obtain ⟨rt,registers,mem,pct⟩:=Machine.evalMath .opening ops _ _ s pc arithmetic nz (prefixReads b l q bl bq s ixSafe)
  obtain ⟨index,address,special,allowed⟩:=registerForm b l q bl bq
  have scratch (r : Reg) (outside : r∉[Reg.x6,.x7,.x8,.x12,rowReg b]) : t.getReg r=s.getReg r:=by
    rw [show t.getReg r=((ops.foldl bump original) r).eval s from registers r]
    rw [preserved ops r original (fun c member eqv=>outside (eqv ▸ (List.contains_iff_mem.mp (List.all_eq_true.mp allowed c member))))]
    cases r <;> rfl
  have targetPtr : t.getReg .x19=W dest := (scratch .x19 (by cases b <;> decide)).trans ptr
  have fromPtr : t.getReg .x12=W (targetAddr i q) := (registers .x12).trans
    ((congrArg (Expr.eval s) address).trans (addressValue b l q i s state))
  have cp:=Machine.evalCopy .opening p _ _ (targetAddr i q) dest t pct copy (show Reg.x6≠.x12 by decide) (show Reg.x6≠.x19 by decide) fromPtr targetPtr safe
    (by change targetAddr i q+0+Machine.bytesOf p.widths≤MEMORY_BYTES;rw [Nat.add_zero,length];exact sb)
    (Or.inl (by change targetAddr i q+0+Machine.bytesOf p.widths≤dest+0;rw [Nat.add_zero,Nat.add_zero,length];exact disjoint))
  have next : u.pc=pcAt (bumpPC b l q):=cp.endPC
  have bumpRun : Runs .opening u (afterField b l q s) 1 1:=
    Machine.one endSmall next (advance b q) (Machine.stood inc) rfl
  have get (r : Reg) (ne : Reg.x19≠r) : (afterField b l q s).getReg r=u.getReg r :=
    MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne)
  have mem2 : (afterField b l q s).mem=u.mem:=rfl
  refine ⟨(rt.trans cp.run).trans bumpRun,?_,?_,?_,?_,?_,?_⟩
  · rw [nextField];exact (congrArg (·+4) next).trans (pc_succ ..).symm
  · change u.getReg .x19+signExtend12 _=_
    rw [show u.getReg .x19=t.getReg .x19 from cp.regs .x19 (by decide),targetPtr,imm];exact (BitVec.ofNat_add ..).symm
  · exact (get _ (by decide)).trans ((cp.regs _ (by decide)).trans ((registers .x8).trans
      ((congrArg (Expr.eval s) index).trans (indexValue b l q i s state))))
  · intro h
    have r7:=special h
    constructor
    · exact (get _ (by decide)).trans ((cp.regs _ (by decide)).trans ((registers .x7).trans
        ((congrArg (Expr.eval s) r7.1).trans (laneValue b l q i s state (by omega)))))
    · exact (get _ (by cases b <;> decide)).trans ((cp.regs _ (by cases b <;> decide)).trans
        ((registers (rowReg b)).trans ((congrArg (Expr.eval s) r7.2).trans (rowValue b l q i s state (by omega)))))
  · intro r hr
    simp only [saved,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    have ext : r∉[Reg.x6,.x7,.x8,.x12,rowReg b]:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.2⟩
    exact (get r (Ne.symm hr.2.2.2.2.1)).trans ((cp.regs r (Ne.symm hr.1)).trans (scratch r ext))
  · have m : Moved t u (targetAddr i q) dest (widthAt b q):=by
      have eq:=cp.bytes;change Moved t u (_+0) (_+0) (Machine.bytesOf p.widths) at eq
      simpa only [Nat.add_zero,length] using eq
    exact m.congr mem.symm mem2
end CommitGolfCandidate.S4.Open
