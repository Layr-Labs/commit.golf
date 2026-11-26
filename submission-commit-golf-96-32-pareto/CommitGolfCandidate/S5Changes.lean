import CommitGolfCandidate.S5Cursor
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
inductive Move where | message | row | rowEnd | node | nodeEnd | count
  deriving DecidableEq

def Move.reg : Move→Reg
  | .message=>.x21 | .row|.rowEnd=>.x22 | .node|.nodeEnd=>.x23 | .count=>.x20
def Move.op : Move→Instr
  | .message=>.ADD .x21 .x21 .x25
  | .row=>.ADD .x22 .x22 .x26
  | .rowEnd=>.ADD .x22 .x22 .x27
  | .node=>.ADD .x23 .x23 .x25
  | .nodeEnd=>.ADDI .x23 .x23 192
  | .count=>.ADDI .x20 .x20 4095

def changes (i : Fin 256) : List Move :=
  (if i.val%16=15 then [.message] else [])++
  (if i.val%42=41 then [.row] else if i.val=255 then [.rowEnd] else [])++
  (if i.val%128=127 then [.node] else [])++
  (if i.val=255 then [.count] else [])
theorem changes_correct : ∀ i : Fin 256,(changes i).map Move.op=updates i := by decide +kernel

def Move.delta (c : Move) (s : MachineState) : Word :=
  match c with
  | .message=>s.getReg .x25 | .row=>s.getReg .x26 | .node=>s.getReg .x25 | .rowEnd=>s.getReg .x27
  | .nodeEnd=>192 | .count=> -1

private theorem one_write (c : Move) (s : MachineState) :
    execInstrBr s c.op=(s.setReg c.reg (s.getReg c.reg+c.delta s)).setPC (s.pc+4) := by cases c <;> rfl
private theorem never_zero (c : Move) : c.reg≠.x0 := by cases c <;> decide
private theorem stride_preserved (c x : Move) (s : MachineState) : x.delta (execInstrBr s c.op)=x.delta s := by
  cases c <;> cases x <;> rfl
private theorem moves_reg (c : Move) (s : MachineState) (r : Reg) :
    (execInstrBr s c.op).getReg r = if c.reg=r then s.getReg r+c.delta s else s.getReg r := by
  rw [one_write,MachineState.getReg_setPC];by_cases same : c.reg=r
  · subst r;rw [if_pos rfl,MachineState.getReg_setReg_eq (never_zero c)]
  · rw [if_neg same,MachineState.getReg_setReg_ne _ _ _ _ same]

def applyDeltas (s : MachineState) : List Move→Word→Word
  | [],v=>v
  | c::cs,v=>applyDeltas s cs (v+c.delta s)

private theorem delta_preserved (s : MachineState) (c : Move) (cs : List Move) (v : Word) :
    applyDeltas (execInstrBr s c.op) cs v=applyDeltas s cs v := by
  induction cs generalizing v with
  | nil=>rfl
  | cons x xs ih=>simp only [applyDeltas,stride_preserved,ih]

theorem reg_effect (cs : List Move) (s : MachineState) (r : Reg) :
    ((cs.map Move.op).foldl execInstrBr s).getReg r =
      applyDeltas s (cs.filter (fun c=>c.reg==r)) (s.getReg r) := by
  induction cs generalizing s with
  | nil=>rfl
  | cons c cs ih=>
    simp only [List.map_cons,List.foldl_cons,ih,delta_preserved,moves_reg,List.filter_cons]
    by_cases eq:c.reg=r <;> simp [eq,applyDeltas]

theorem frame_effect (cs : List Move) (s : MachineState) :
    let t:=(cs.map Move.op).foldl execInstrBr s
    t.pc=s.pc+BitVec.ofNat 64 (4*cs.length) ∧ t.mem=s.mem := by
  induction cs generalizing s with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons,List.foldl_cons,List.length_cons]
    have ⟨p,m⟩:=ih (execInstrBr s c.op)
    have p0 : (execInstrBr s c.op).pc=s.pc+4 := by cases c <;> rfl
    have m0 : (execInstrBr s c.op).mem=s.mem := by cases c <;> rfl
    refine ⟨?_,m.trans m0⟩
    rw [p,p0,show 4*(cs.length+1)=4+4*cs.length by omega,BitVec.ofNat_add,BitVec.add_assoc];rfl

def selected (i : Fin 256) (r : Reg) : List Move :=
  match r with
  | .x21=>if i.val%16=15 then [.message] else []
  | .x22=>if i.val%42=41 then [.row] else if i.val=255 then [.rowEnd] else []
  | .x23=>if i.val%128=127 then [.node] else []
  | .x20=>if i.val=255 then [.count] else []
  | _=>[]

private theorem selected_correct (r : Reg) :
    ∀ i : Fin 256,(changes i).filter (fun c=>c.reg==r)=selected i r := by
  cases r <;> decide +kernel

theorem updates_read (s : MachineState) (i : Fin 256) (r : Reg) :
    ((updates i).foldl execInstrBr s).getReg r=applyDeltas s (selected i r) (s.getReg r) := by
  rw [←changes_correct i,reg_effect,selected_correct]
end CommitGolfCandidate.S5Machine
