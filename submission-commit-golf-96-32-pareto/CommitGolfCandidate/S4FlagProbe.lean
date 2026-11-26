import CommitGolfCandidate.S4CheckedRow
import CommitGolfCandidate.S4Seen
import CommitGolfCandidate.S4Table
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt Digest)
abbrev caller (r : Reg) := r∈[Reg.x8,.x9,.x18,.x19,.x5,.x13,.x11,.x23,.x27]
theorem PendingRow.transfer {x : CheckInput} {s t : MachineState} {r : Nat} (old : PendingRow x s r)
    (regs : ∀ v,caller v → t.getReg v=s.getReg v) (data : InputsStill x t) : PendingRow x t r :=
  ⟨⟨(regs _ (by decide)).trans old.mode,(regs _ (by decide)).trans old.kind,(regs _ (by decide)).trans old.width,
     (regs _ (by decide)).trans old.three,(regs _ (by decide)).trans old.root,data⟩,
   (regs _ (by decide)).trans old.index,(regs _ (by decide)).trans old.value,(regs _ (by decide)).trans old.proof,(regs _ (by decide)).trans old.count⟩

def probeOps : List Sym.Calc := [.addi .x14 .x20 768,.lbu .x7 .x14 0,.slli .x15 .x20 5,.addi .x6 .x0 1,.slli .x6 .x6 11,
  .addi .x6 .x6 0,.add .x15 .x15 .x6,.addi .x1 .x0 256]
private theorem known : (Fragment.arithmetic probeOps).valid .check 4343 4351:=by decide
def flagBit (present : Bool) : Word:=if present then 1 else 0
structure Probe (o : Oracle) (s t : MachineState) (u : Nat) (hit : Bool) : Prop where
  run : CheckRuns o s t (if hit then 10 else 9) 0
  pc : t.pc=pcAt (if hit then 4364 else 4353)
  faddr : t.getReg .x14=W (flagAddr u)
  addr : t.getReg .x15=W (capAddr u)
  root : t.getReg .x1=W 256
  keep : ∀ v,caller v → t.getReg v=s.getReg v
  mem : t.mem=s.mem

attribute [local irreducible] Sym.evaluated
set_option maxHeartbeats 900000 in
set_option maxRecDepth 5000 in
theorem probeFlag (o : Oracle) (s : MachineState) (u : Nat) (inside : u<342) (hit : Bool) (pc : s.pc=pcAt 4343)
    (idx : s.getReg .x20=W u) (flag : byte s (flagAddr u)=if hit then 1 else 0) :
    ∃ t,Probe o s t u hit := by
  let t:=Sym.evaluated probeOps s
  let expr:=Sym.mkOp .add (Sym.mkOp .add (.reg .x20) (.lit (W 768))) (.lit (W 0))
  have flat : expr.eval s=W (flagAddr u):=by
    simp only [expr,Sym.eval_mkOp,Sym.Expr.eval,Sym.Bin.apply,idx]
    apply (BitVec.add_zero _).trans;exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold flagAddr;omega))
  have reads : Sym.requirements Sym.original probeOps=[(expr,1)]:=rfl
  obtain ⟨run,regs,mem,last⟩:=evalMath .check probeOps 4343 4351 s pc known
    (fun c h=>bne_iff_ne.mp (List.all_eq_true.mp (by decide : probeOps.all (fun c=>c.dst != .x0)=true) c h))
    (fun e m=>by rw [reads] at m;rcases List.mem_singleton.mp m with rfl;change accessValid (expr.eval s) 1=true
                 rw [flat];exact Safe.valid ⟨by unfold flagAddr MEMORY_BYTES;omega,Nat.mod_one _⟩)
  have first : t.getReg .x14=W (flagAddr u):=by
    apply (regs .x14).trans;change s.getReg .x20+W 768=_;rw [idx];exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold flagAddr;omega))
  have slot : t.getReg .x15=W (capAddr u):=by
    apply (regs .x15).trans;change (s.getReg .x20 <<< 5)+W 2048=_
    rw [idx,shifted];exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by unfold capAddr;omega))
  have val : t.getReg .x7=flagBit hit:=by
    apply (regs .x7).trans;change (s.getByte (expr.eval s)).zeroExtend 64=_;rw [flat]
    change (byte s (flagAddr u)).zeroExtend 64=_;rw [flag];cases hit <;> rfl
  have edge:=alternate .check 4351 4353 4364 .x7 .x0 true (by decide) (by decide) rfl t last
  have choice : ((t.getReg .x7==t.getReg .x0)==true)=(!hit):=by rw [val];cases hit <;> rfl
  rw [choice] at edge
  let z:=t.setPC (pcAt (if hit then 4364 else 4353))
  have steps : CheckRuns o s z (if hit then 10 else 9) 0:=by
    cases hit <;> exact (ofRuns o run).trans (ofRuns o edge)
  refine ⟨z,⟨steps,rfl,first,slot,(regs .x1).trans rfl,?_,mem⟩⟩
  intro r safe
  have neither : ∀ v : Reg,caller v → v∉[Reg.x1,.x6,.x7,.x14,.x15]:=by intro v;cases v <;> decide
  exact MachineState.getReg_setPC.trans (outsideCalc probeOps s t regs [.x1,.x6,.x7,.x14,.x15] (by decide) r (neither r safe))
end CommitGolfCandidate.S4.Machine
