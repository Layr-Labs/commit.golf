import CommitGolfCandidate.R1bCodecBytes
namespace CommitGolfCandidate.R1b.Codec
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Machine
open R1bPC (pcAt)
def Input (d : Bool) (s : MachineState) : Prop :=
  s.getReg .x18=W proofBase
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
  have shape : t.getReg .x21=W proofBase ∧ t.getReg .x22=W (proofBase+67488):=by
    have base : s.getReg .x18=W proofBase := args
    have addZero : s.getReg .x18+(0 : Word)=s.getReg .x18 := BitVec.add_zero _
    have first : t.getReg .x21=s.getReg .x18 := addZero
    have tail : t.getReg .x22=s.getReg .x18+W 67488 := by
      change (s.getReg .x18+(0 : Word))+_ = _
      rw [addZero]
      apply congrArg (s.getReg .x18 + ·)
      change ((32#64 <<< (11 : Nat)) + 1952#64) = BitVec.ofNat 64 67488
      decide
    have moved := congrArg (fun x : Word=>x+W 67488) base
    exact ⟨first.trans base,tail.trans (moved.trans (BitVec.ofNat_add ..).symm)⟩
  refine ⟨t,⟨⟨(memStart d s).still mem,shape.1,shape.2,saved⟩,?_⟩,?_⟩
  · exact ip.trans (congrArg pcAt (by cases d <;> rfl))
  · have price : Sym.price (firstOps d)=5:=by cases d <;> rfl
    simpa only [len,price] using run

def bodySteps (d : Bool) := if d then 10129 else 11173
theorem run (law : CodeLaw) (d : Bool) (s : MachineState) (pc : s.pc=pcAt (entry d)) (args : Input d s) :
    ∃ t,Common d s t 352 1396 ∧ t.pc=pcAt (donePC d) ∧
      Runs (program d) s t (bodySteps d) (bodySteps d) := by
  obtain ⟨u,init,header⟩:=enter d s pc args
  obtain ⟨t,last,body⟩:=manyBytes law d s u 352 le_rfl init
  have sum : 5+(bytePC d 352-bytePC d 0)=bodySteps d:=by cases d <;> decide
  exact ⟨t,last.toCommon,last.pc,by simpa only [sum] using header.trans body⟩
end CommitGolfCandidate.R1b.Codec
