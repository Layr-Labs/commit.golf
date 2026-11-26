import CommitGolfCandidate.S5BatchFrame
import CommitGolfCandidate.S5SiblingLookup
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape node)
open Writer (widths)

def outerRegs : List Reg := [.x3,.x8,.x9,.x18,.x20,.x21,.x22,.x25,.x26,.x27]
def OuterKeeps (s t : MachineState) := ∀ r∈outerRegs,t.getReg r=s.getReg r
theorem OuterKeeps.then {s t u} (a : OuterKeeps s t) (b : OuterKeeps t u) : OuterKeeps s u := fun r hr=>(b r hr).trans (a r hr)

structure PutField (s t : MachineState) (e : EmitSite) (tree : Levels) (fs : List S5.Field) (x : Nat) : Prop where
  run : Runs s t (emitCycles e (widths fs)) (emitCycles e (widths fs))
  pc : t.pc=pcAt (e.pc+2)
  cursor : FieldCursor tree t (fs++[(e.width,x)])
  low : Writer.Below s t proofBase
  keep : ∀ r : Reg,Writer.preserved r → r≠.x1 → r≠.x11 → t.getReg r=s.getReg r

theorem put_field (s : MachineState) (e : EmitSite) (fs : List S5.Field) (tree : Levels) (a bytes : Nat) (raw : BitVec (8*bytes))
    (cur : FieldCursor tree s fs) (pc : s.pc=pcAt e.pc) (src : s.getReg .x10=W a) (aa : a%8=0)
    (low : a+32≤proofBase) (bound : widths fs≤555170) (fit : WireFits tree → raw.toNat<2^e.width)
    (read : readBuffer s a bytes=raw) (words : 8*(Writer.parts e.width).length≤bytes) :
    PutField s (emitted e (widths fs) s) e tree fs raw.toNat := by
  obtain ⟨run,ip,newCursor,frame,keep⟩:=emit_field s e (WireFits tree) _ _ a _ cur pc src aa low bound
    (fun valid=>field_source s a e.width bytes raw read (fit valid) words aa) fit
  exact ⟨run,ip,cursor_append newCursor fit,fun j hj=>frame j (by omega),keep⟩

theorem PutField.outer {s t e tree fs x} (p : PutField s t e tree fs x) : OuterKeeps s t := by
  intro r h
  apply p.keep
  all_goals cases r <;> simp [outerRegs,Writer.preserved] at *

def siblingField (t : Levels) (i : Index) (d : Nat) : S5.Field := (S5.bits d,(node t d (mate i d)).toNat)
theorem batch_sibling (s : MachineState) (l : Fin 14) (i : Index) (xs seen : List Index) (tree : Levels) (salt : SaltTape)
    (size : xs.length≤LENGTH) (env : InputRows s xs seen tree salt) (fs : List S5.Field) (bound : widths fs≤555170)
    (cur : FieldCursor tree s fs) (pc : s.pc=pcAt (179+12*l.val)) (gp : s.getReg .x3=W 2048)
    (idx : s.getReg .x14=W (indexAbove i (l.val+1))) :
    let field:=siblingField tree i (l.val+1)
    let cost:=10+emitCycles (.sibling l) (widths fs)
    ∃ t,Runs s t cost cost ∧ t.pc=pcAt (179+12*(l.val+1)) ∧ t.getReg .x14=W (indexAbove i (l.val+2)) ∧
      FieldCursor tree t (fs++[field]) ∧ InputRows t xs seen tree salt ∧ OuterKeeps s t := by
  let d:=l.val+1
  let k:=Lookup.batch l
  let u:=k.after s
  let a:=nodeAddress d (mate i d)
  have jbound : indexAbove i d<2^64 := by
    unfold indexAbove S4.nodeIndex
    have h:=i.isLt;change i.val<16777216 at h;have :=Nat.div_le_self i.val (S4.span d);omega
  obtain ⟨head,ip,mem,idx',source,keeps⟩:=sibling_lookup s k _ jbound pc gp idx (env.table _ (by change l.val+1<25;omega))
  have dlim : d<24:=by dsimp [d];omega
  have mateOk:=mate_bound i d (by dsimp [d];omega) dlim
  have selected:=node_ok d _ mateOk
  have safe : ∀ r, r∈outerRegs ∨ r=.x19 ∨ r=.x23 ∨ r=.x24 → u.getReg r=s.getReg r := by
    intro r hr;apply keeps <;> intro e <;> subst r <;> simp [outerRegs,k,Lookup.dst] at hr
  have ready : FieldCursor tree u fs:=cursor_same cur mem (safe _ (by simp)) (safe _ (by simp))
    (safe _ (by simp [outerRegs])) (safe _ (by simp))
  let e:=EmitSite.sibling l
  have start : u.pc=pcAt e.pc := by rw [show u.pc=_ from ip];apply congrArg pcAt;change 179+12*l.val+10=189+12*l.val;omega
  have raw :=env.sources.node d (show d≤LOG_LENGTH from dlim.le) _ mateOk
  have recBounds : 8*(Writer.parts e.width).length≤32 :=
    (by decide +kernel : ∀ j : Fin 14,8*(Writer.parts (EmitSite.sibling j).width).length≤32) l
  have more:=put_field u e fs tree a 32 _ ready start source selected.2.2 (selected.2.1.trans (by decide)) bound
    (fun good=>good d (by dsimp [d];omega) (mate i d)) ((read_congr_mem u s a 32 mem).trans raw) recBounds
  let t:=emitted e (widths fs) u
  refine ⟨t,head.trans more.run,more.pc.trans (congrArg pcAt (by change 189+12*l.val+2=179+12*(l.val+1);omega)),?_,
    more.cursor,inputs_below (inputs_mem env mem) size more.low,?_⟩
  · exact (more.keep .x14 (by simp [Writer.preserved]) (by decide) (by decide)).trans (idx'.trans
      (congrArg W (above_next i d (by dsimp [d];omega)).symm))
  · exact OuterKeeps.then (fun r hr=>safe r (Or.inl hr)) more.outer
end CommitGolfCandidate.S5Machine.Open
