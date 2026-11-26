import CommitGolfCandidate.S4CheckRecord
import CommitGolfCandidate.S4Dispatch

set_option Elab.async false
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest pcAt)
def rowLimit (b : Bool) := if b then 4343 else 2634
def recordFuel (b : Bool) := 111+pathPrice b (pathLevels b)
def recordCalls (b : Bool) := 4+pathLevels b

structure PendingRow (x : CheckInput) (s : MachineState) (r : Nat) extends Env x s : Prop where
  index : s.getReg .x8=W (indexBase+8*r)
  value : s.getReg .x9=W (valueBase+256*r)
  proof : s.getReg .x18=W (proofBase+recordBytes (decide (x.positions.card=BATCH))*(r+1))
  count : s.getReg .x19=W (x.positions.card-r)

theorem checkedRow (o : Oracle) (x : CheckInput) (b : Bool) (r : Nat) (s : MachineState) (br : r<x.positions.card)
    (choice : b=decide (x.positions.card=BATCH)) (pc : s.pc=pcAt (rowStart b)) (env : Env x s) (cursor : Cursor x s r) :
    ∃ t,CheckRuns o s t (recordFuel b) (recordCalls b) ∧ t.pc=pcAt (rowLimit b) ∧ PendingRow x t r ∧
      SameOutside s t 256 352 ∧ t.getReg .x20=W (nodeIndex ((readView x).idx r).val (pathLevels b)) ∧
      readBuffer t 256 32=recordAt .packed o.compression (readView x) r (pathLevels b) ((readView x).peers r) := by
  obtain ⟨u,leaf⟩:=checkLeaf o x b r s br choice pc env cursor
  have env2 : Env x u:=⟨(leaf.keep _ (by decide)).trans env.mode,(leaf.keep _ (by decide)).trans env.kind,
    (leaf.keep _ (by decide)).trans env.width,(leaf.keep _ (by decide)).trans env.three,(leaf.keep _ (by decide)).trans env.root,
    env.data.scratch leaf.frame⟩
  obtain ⟨t,row⟩:=recordPath o x b r (pathLevels b) u br choice le_rfl leaf.next leaf.idx leaf.proof leaf.data env2
  have frame:=bothScratch leaf.frame row.frame
  have keep (v : Reg) (safe : pathKeep v) : t.getReg v=s.getReg v:=(row.keep v safe).trans (leaf.keep v safe)
  have next : nodePC b (pathLevels b)=rowLimit b:=by
    cases b with
    | false=>exact pathEnd.1
    | true=>exact pathEnd.2.1
  have off : fieldOffset b (pathLevels b)=recordBytes b:=by cases b <;> decide
  refine ⟨t,leaf.run.trans row.run,row.pc.trans (congrArg pcAt next),?_,frame,row.index,row.digest⟩
  refine ⟨⟨(keep _ (by decide)).trans env.mode,(keep _ (by decide)).trans env.kind,(keep _ (by decide)).trans env.width,
    (keep _ (by decide)).trans env.three,(keep _ (by decide)).trans env.root,env.data.scratch frame⟩,
    (keep _ (by decide)).trans cursor.index,(keep _ (by decide)).trans cursor.value,?_,(keep _ (by decide)).trans cursor.count⟩
  apply row.cursor.trans;apply congrArg W;rw [siblingPtr,off,←choice,Nat.mul_succ];omega

def endOfRows (b : Bool) := if b then 4385 else 2656
def latchPC (b : Bool) := if b then 4380 else 2651
def advanceOps : List Sym.Calc := [.addi .x8 .x8 8,.addi .x9 .x9 256,.addi .x19 .x19 4095]
def advanceState (s : MachineState) := Sym.evaluated advanceOps s
set_option maxRecDepth 3500 in
private theorem latchSites : ∀ b : Bool,
    (Fragment.arithmetic advanceOps).valid .check (latchPC b) (latchPC b+3) ∧
    conditional .check (latchPC b+3) (latchPC b+5) .x19 .x0 true ∧ directs .check (latchPC b+4) (rowStart b) ∧
    latchPC b+5=endOfRows b :=by decide

structure RowEdge (o : Oracle) (x : CheckInput) (b : Bool) (s t : MachineState) (r n : Nat) : Prop where
  run : CheckRuns o s t n 0
  pc : t.pc=pcAt (if r+1<x.positions.card then rowStart b else endOfRows b)
  env : Env x t
  cursor : Cursor x t (r+1)
  mem : t.mem=s.mem

theorem advanceRow (o : Oracle) (x : CheckInput) (b : Bool) (s : MachineState) (r : Nat)
    (br : r<x.positions.card) (pc : s.pc=pcAt (latchPC b)) (f : PendingRow x s r) : ∃ t n,n≤5 ∧ RowEdge o x b s t r n := by
  obtain ⟨known,yes,no,limit⟩:=latchSites b
  obtain ⟨step,regs,mem,after⟩:=evalMath .check advanceOps _ _ s pc known
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : advanceOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun _ h=>by cases h)
  let u:=advanceState s
  have idx : u.getReg .x8=W (indexBase+8*(r+1)):=by
    apply (regs .x8).trans;change s.getReg .x8+W 8=_;rw [f.index]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  have value : u.getReg .x9=W (valueBase+256*(r+1)):=by
    apply (regs .x9).trans;change s.getReg .x9+W 256=_;rw [f.value]
    exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))
  have cnt : u.getReg .x19=W (x.positions.card-(r+1)):=by
    apply (regs .x19).trans;change s.getReg .x19+18446744073709551615=_;rw [f.count]
    exact (prev _ (by omega)).trans (congrArg W (by omega))
  have keep (reg : Reg) (safe : reg∉[Reg.x8,.x9,.x19]) : u.getReg reg=s.getReg reg:=
    outsideCalc advanceOps s u regs _ rfl reg safe
  have edge:=alternate .check (latchPC b+3) (latchPC b+5) (rowStart b) .x19 .x0 true yes no rfl u after
  let t:=u.setPC (pcAt (if r+1<x.positions.card then rowStart b else endOfRows b))
  have bound:=boundedCount x
  have test : ((u.getReg .x19==u.getReg .x0)==true)=decide (x.positions.card≤r+1):=by
    change ((u.getReg .x19==W 0)==true)=_;rw [cnt,eqNatural _ _ (by omega) (by decide)]
    by_cases e : x.positions.card≤r+1
    · rw [decide_eq_true e,decide_eq_true (by omega : x.positions.card-(r+1)=0)];rfl
    · rw [decide_eq_false e,decide_eq_false (by omega : ¬x.positions.card-(r+1)=0)];rfl
  rw [test,limit] at edge
  have nextEnv : Env x t:=⟨(keep _ (by decide)).trans f.mode,(keep _ (by decide)).trans f.kind,
    (keep _ (by decide)).trans f.width,(keep _ (by decide)).trans f.three,(keep _ (by decide)).trans f.root,
    f.data.regs (show t.mem=s.mem from mem)⟩
  have nextCur : Cursor x t (r+1):=⟨idx,value,(keep _ (by decide)).trans f.proof,cnt⟩
  by_cases more : r+1<x.positions.card
  · rw [decide_eq_false (Nat.not_le_of_lt more)] at edge
    have leap : Runs .check u t 2 2:=by dsimp only [t];rw [if_pos more];exact edge
    exact ⟨t,5,by decide,⟨(ofRuns o step).trans (ofRuns o leap),rfl,nextEnv,nextCur,mem⟩⟩
  · rw [decide_eq_true (Nat.le_of_not_gt more)] at edge
    have leap : Runs .check u t 1 1:=by dsimp only [t];rw [if_neg more];exact edge
    exact ⟨t,4,by decide,⟨(ofRuns o step).trans (ofRuns o leap),rfl,nextEnv,nextCur,mem⟩⟩
end CommitGolfCandidate.S4.Machine
