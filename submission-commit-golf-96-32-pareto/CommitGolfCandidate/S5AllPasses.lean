import CommitGolfCandidate.S5PlainPass
import CommitGolfCandidate.S5TreeStart
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (PairCoins)

set_option maxRecDepth 20000
attribute [local irreducible] readBuffer execute leavesDone
def stage (n : Nat) : Height:=⟨n%24,by omega⟩
def boundary : Nat→Nat
  | 0=>7230
  | n+1=>passEnd (stage n)
def sumCost (f : Height→Nat) : Nat→Nat
  | 0=>0
  | n+1=>sumCost f n+f (stage n)

theorem next_header (d : Height) : boundary d.val=passHeader d := (by decide +kernel : ∀ k : Height,boundary k.val=passHeader k) d
theorem stage_sums : sumCost passSteps 24=40999727 ∧ sumCost passCycles 24=120231537 ∧
    sumCost (fun h=>count h*calls h) 24=11318830 := by decide +kernel

private theorem initial_common (s : MachineState) (a : AtLeaf s LENGTH) : Common (parentSetup.foldl execInstrBr s) := by
  have stride (q : MachineState) : let z:=parentSetup.foldl execInstrBr q
      z.getReg .x25=4032 ∧ z.getReg .x26=4032 ∧ z.getReg .x27=4032 := by
    simp [parentSetup,execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12] <;> decide
  exact ⟨a.selector,a.len,a.kind,a.base,a.root,a.scratch,(stride s).1,(stride s).2.1,(stride s).2.2⟩

theorem combined (stages : ∀ d : Height,StageLaw d) (o : Oracle) (s : MachineState) (base : Nat→Output) (salt : Late.SaltTape)
    (entry : s.pc=pcAt 7230) (regs : Common s) (startTree : TreeState o.compression base salt 0 s) (n : Nat) (hn : n≤24) :
    ∃ t, t.pc=pcAt (boundary n) ∧ Common t ∧ TreeState o.compression base salt n t ∧
      Runs .commit true o s t (sumCost passSteps n) (sumCost passCycles n) (sumCost (fun h=>count h*calls h) n) := by
  induction n with
  | zero=>exact ⟨s,entry,regs,startTree,runs_id .commit true o s⟩
  | succ n ih=>
    obtain ⟨t,ip,ctx,tree,before⟩:=ih (by omega)
    let h : Height:=⟨n,by omega⟩
    obtain ⟨u,exit,next,result,run⟩:=stages h o t base salt (ip.trans (congrArg pcAt (next_header h))) ctx tree
    have id : stage n=h := Fin.ext (Nat.mod_eq_of_lt h.isLt)
    simp only [boundary,sumCost,id]
    exact ⟨u,exit,next,result,runs_comp before run⟩

private theorem root_run_from (stages : ∀ d : Height,StageLaw d) (o : Oracle) (s : MachineState)
    (base : Nat→Output) (salt : Late.SaltTape) (regs : AtLeaf s LENGTH) (tree0 : TreeState o.compression base salt 0 s) :
    ∃ t, t.pc=pcAt 18478 ∧ Common t ∧ TreeState o.compression base salt 24 t ∧
      Runs .commit true o s t 40999733 120231543 11318830 := by
  have old : s.pc=pcAt 7224:=regs.pc.trans (by rw [if_neg (Nat.lt_irrefl _)])
  let u:=parentSetup.foldl execInstrBr s
  have common:=initial_common s regs
  have setup : Runs .commit true o s u 6 6 0 := runs_pure (parents_setup_run s old)
  have frame:=header_properties parentSetup s (fun op mem=>List.all_eq_true.mp (by decide : parentSetup.all setupOp) op mem)
  have pc : u.pc=pcAt 7230 := by rw [show u.pc=_ from frame.2,old];rfl
  obtain ⟨t,last,cm,tree,parents⟩:=combined stages o u base salt pc common (transfer_tree tree0 frame.1) 24 le_rfl
  have finalPC : boundary 24=18478 := by decide +kernel
  rw [finalPC] at last
  obtain ⟨steps,cycles,calls⟩:=stage_sums
  rw [steps,cycles,calls] at parents
  have run:=runs_comp setup parents
  rw [show 6+40999727=40999733 by decide,show 6+120231537=120231543 by decide,Nat.zero_add] at run
  exact ⟨t,last,cm,tree,run⟩

theorem through_root (stages : ∀ d : Height,StageLaw d) (o : Oracle) (m : Message) (ws : List PairCoins)
    (len : ws.length=pairCount) :
    let base : Nat → Output := fun k=>(initialList o.compression m (wordTape ws))[k]?.getD 0
    let s:=leavesDone o m ws
    ∃ t, t.pc=pcAt 18478 ∧ Common t ∧ TreeState o.compression base (wordTape ws) 24 t ∧
      Runs .commit true o s t 40999733 120231543 11318830 :=
  root_run_from stages o (leavesDone o m ws) _ (wordTape ws) (leaves_done_regs o m ws len) (initial_tree o m ws len)
end CommitGolfCandidate.S5Machine
