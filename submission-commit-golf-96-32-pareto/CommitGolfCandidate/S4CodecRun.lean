import CommitGolfCandidate.S4CodecBytes

set_option Elab.async false
namespace CommitGolfCandidate.S4.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open Late (pcAt)
def Input (d : Bool) (s : MachineState) : Prop :=
  if d then s.getReg .x18=W proofBase else s.getReg .x19=W (proofBase+70410) ∧ s.getReg .x11=W 70410
private theorem firstListed (d : Bool) : listed (program d) (entry d) ((firstOps d).map Sym.Calc.instr) := by cases d <;> decide
private theorem enter (d : Bool) (s : MachineState) (pc : s.pc=pcAt (entry d)) (args : Input d s) :
    ∃ t,ByteState d s t 0 ∧ Runs (program d) s t 5 5 := by
  let t:=Sym.evaluated (firstOps d) s
  have len : (firstOps d).length=5:=by cases d <;> rfl
  obtain ⟨run,regs,mem,ip⟩:=calcRegs (program d) s (firstOps d) (entry d) pc
    (by cases d <;> decide) (matchesListed (firstListed d)) (by cases d <;> rfl) (by cases d <;> rfl)
  have saved (r : Reg) (hr : stable r) : t.getReg r=s.getReg r:=by
    have nr : r∉[Reg.x21,.x22]:=by
      rcases hr with ⟨keep,a⟩;unfold controlReg at keep;simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at keep ⊢;exact ⟨keep.1,a⟩
    exact outsideCalc _ s t regs _ (by cases d <;> decide) r nr
  have shape : t.getReg .x21=W proofBase ∧ t.getReg .x22=W (proofBase+70080):=by
    change (Sym.evaluated (firstOps d) s).getReg .x21=_ ∧ (Sym.evaluated (firstOps d) s).getReg .x22=_
    rw [regs .x21,regs .x22]
    cases d
    · obtain ⟨cursor,size⟩:=args
      change s.getReg .x19-s.getReg .x11=_ ∧ (s.getReg .x19-s.getReg .x11)+70080 = W (proofBase+70080)
      rw [cursor,size];exact ⟨rfl,rfl⟩
    · change s.getReg .x18=W proofBase at args
      change s.getReg .x18+0=_ ∧ (s.getReg .x18+0)+70080 = W (proofBase+70080)
      rw [args];exact ⟨rfl,rfl⟩
  refine ⟨t,⟨⟨(memStart d s).still mem,shape.1,shape.2,saved⟩,?_⟩,?_⟩
  · exact ip.trans (congrArg pcAt (by cases d <;> rfl))
  · have price : Sym.price (firstOps d)=5:=by cases d <;> rfl
    simpa only [len,price] using run

def bodySteps (d : Bool) := if d then 9498 else 10477
theorem run (law : CodeLaw) (d : Bool) (s : MachineState) (pc : s.pc=pcAt (entry d)) (args : Input d s) :
    ∃ t,Common d s t 330 1309 ∧ t.pc=pcAt (donePC d) ∧
      Runs (program d) s t (bodySteps d) (bodySteps d) := by
  obtain ⟨u,init,header⟩:=enter d s pc args
  obtain ⟨t,last,body⟩:=manyBytes law d s u 330 le_rfl init
  have sum : 5+(bytePC d 330-bytePC d 0)=bodySteps d:=by cases d <;> decide
  exact ⟨t,last.toCommon,last.pc,by simpa only [sum] using header.trans body⟩
end CommitGolfCandidate.S4.Codec
