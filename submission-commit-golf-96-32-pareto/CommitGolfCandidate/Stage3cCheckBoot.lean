import CommitGolfCandidate.Stage3cCheckInput
import CommitGolfCandidate.Stage3cCheckEdges
import CommitGolfCandidate.Stage3cCheckCalc
import CommitGolfCandidate.Stage3cCheckLeafData
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)
def incoming : List Sym.Calc := [.addi .x8 .x11 0,.addi .x9 .x13 0,.addi .x18 .x14 0,.addi .x19 .x15 0,
  .add .x20 .x15 .x17,.addi .x21 .x0 0,.addi .x22 .x0 0,.addi .x23 .x16 0]
def workspace : List Sym.Calc := [.lui .x24 16,.lui .x25 16,.addi .x25 .x25 256,.lui .x26 16,.addi .x26 .x26 512,
  .lui .x27 16,.addi .x27 .x27 768,.addi .x3 .x0 3]
structure InputRegs (s : MachineState) (x : CheckInput) : Prop where
  root : s.getReg .x8=W rootBase
  indices : s.getReg .x9=W indexBase
  values : s.getReg .x18=W valueBase
  proof : s.getReg .x19=W proofBase
  end_ : s.getReg .x20=W (proofBase+x.proof.length)
  held : s.getReg .x21=0
  bits : s.getReg .x22=0
  num : s.getReg .x23=W x.positions.card
  length : s.getReg .x17=W x.proof.length

def inputRegs : List Reg:=[.x8,.x9,.x18,.x19,.x20,.x21,.x22,.x23,.x17]
theorem InputRegs.kept {s t x} (r : InputRegs s x) (k : ∀ q∈inputRegs,t.getReg q=s.getReg q) : InputRegs t x:=
  ⟨(k _ (by decide)).trans r.root,(k _ (by decide)).trans r.indices,(k _ (by decide)).trans r.values,(k _ (by decide)).trans r.proof,
    (k _ (by decide)).trans r.end_,(k _ (by decide)).trans r.held,(k _ (by decide)).trans r.bits,
    (k _ (by decide)).trans r.num,(k _ (by decide)).trans r.length⟩

private theorem fixed_size (s : MachineState) (q : Reg) (h : q∈inputRegs) : ((workspace.foldl Sym.bump Sym.original) q).eval s=s.getReg q:=by
  cases q <;> first | (exfalso;revert h;decide) | rfl
private theorem input_regs (x : CheckInput) (s : MachineState) (out : Sym.live (initial x) s (incoming.foldl Sym.bump Sym.original)) :
    InputRegs s x := by
  refine ⟨(out _).trans ?_,(out _).trans ?_,(out _).trans ?_,(out _).trans ?_,(out _).trans ?_,
    (out _).trans ?_,(out _).trans ?_,(out _).trans ?_,(out _).trans ?_⟩
  all_goals first | rfl | (change W proofBase+W x.proof.length=_;exact (BitVec.ofNat_add ..).symm) |
    (change W x.positions.card+0#64=_;rw [BitVec.add_zero])

structure Boot (o : Oracle) (x : CheckInput) (s : MachineState) : Prop where
  run : Flow o (initial x) s 18 0
  pc : s.pc=pcAt 225
  mem : s.mem=(initial x).mem
  input : InputRegs s x
  radix : s.getReg .x3=3
  leaf : s.getReg .x24=W leafBuf
  row : s.getReg .x25=W rowBuf
  chain : s.getReg .x26=W chainBuf
  digest : s.getReg .x27=W digestBuf
theorem boot (o : Oracle) (x : CheckInput) (nonempty : 0<x.positions.card) : ∃ s,Boot o x s := by
  let s:=initial x
  let u:=Sym.evaluated incoming s
  obtain ⟨start,regs,mem,pc⟩:=Sym.compiled o incoming 0 s rfl (by decide +kernel) (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have inp:=input_regs x u regs
  have size : x.positions.card≤LENGTH:=by simpa using Finset.card_le_univ x.positions
  have sm : x.positions.card<2^64:=by change x.positions.card≤16777216 at size;omega
  have neq : u.getReg .x23 ≠ 0#64:=by rw [inp.num];intro eq;have n:=congrArg BitVec.toNat eq;simp only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt sm] at n;omega
  have first:=branch o u 8 12 .ne .x23 .x0 (by decide +kernel) pc true (bne_iff_ne.mpr neq)
  let v:=u.setPC (pcAt 12)
  let w:=Sym.evaluated workspace v
  obtain ⟨prep,values,m2,ip⟩:=Sym.compiled o workspace 12 v rfl (by decide +kernel) (by change ∀ e∈([] : List (Sym.Expr×Nat)),_;simp)
  have last:=jump o w 20 225 .x0 (by decide +kernel) ip
  let t:=w.setPC (pcAt 225)
  have keep (q : Reg) (ok : q∈inputRegs) : t.getReg q=u.getReg q:=MachineState.getReg_setPC.trans ((values q).trans ((fixed_size v q ok).trans MachineState.getReg_setPC))
  exact ⟨t,⟨((start.trans first).trans prep).trans last,rfl,m2.trans mem,inp.kept keep,
    MachineState.getReg_setPC.trans (values .x3),MachineState.getReg_setPC.trans (values .x24),
    MachineState.getReg_setPC.trans (values .x25),MachineState.getReg_setPC.trans (values .x26),MachineState.getReg_setPC.trans (values .x27)⟩⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
