import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc.Wire
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 7000
set_option maxHeartbeats 60000

private def dec28 (s : MachineState) := execInstrBr s (.ADDI .x28 .x28 4095)
private theorem decEq (s : MachineState) :
    dec28 s=(s.setReg .x28 (s.getReg .x28-1)).setPC (s.pc+4) := by
  unfold dec28
  simp only [execInstrBr,BitVec.sub_eq_add_neg]
  rfl

private theorem branch28 (m : MachineState) (off : BitVec 13) (v : Word) (pc enter exit : Word)
    (reg : m.getReg .x28=v) (atPC : m.pc=pc) (back : pc+signExtend13 off=enter) (next : pc+4=exit) :
    execInstrBr m (.BNE .x28 .x0 off)=m.setPC (if v=0 then exit else enter) := by
  have zero : m.getReg .x0=0#64:=rfl
  by_cases h : v=0#64
  · simp [execInstrBr,reg,zero,h,atPC,show pc+4#64=exit from next]
  · simp [execInstrBr,reg,zero,h,atPC,back]

private theorem both (s : MachineState) (first second : Instr) :
    ([first,second] : List Instr).foldl execInstrBr s=execInstrBr (execInstrBr s first) second := rfl
private theorem popPC (s : MachineState) (a b : Word) : (s.setPC a).setPC b=s.setPC b := rfl

theorem latchState (s : MachineState) (offset : BitVec 13) (back next : Word)
    (yes : s.pc+4+signExtend13 offset=back) (no : s.pc+4+4=next) :
    ([.ADDI .x28 .x28 4095,.BNE .x28 .x0 offset] : List Instr).foldl execInstrBr s=
      (s.setReg .x28 (s.getReg .x28-1)).setPC (if s.getReg .x28-1=0 then next else back) := by
  have reg : (dec28 s).getReg .x28=s.getReg .x28-1 := by
    rw [decEq,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide : Reg.x28≠.x0)]
  have pc : (dec28 s).pc=s.pc+4 := by rw [decEq];rfl
  have branch:=branch28 (dec28 s) offset _ _ back next reg pc yes no
  apply (both _ _ _).trans
  apply branch.trans
  rw [decEq,popPC]
end CommitGolfCandidate.Trunc.Wire
