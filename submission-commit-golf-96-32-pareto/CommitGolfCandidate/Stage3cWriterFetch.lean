import CommitGolfCandidate.Stage3cWriterCode
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 80000
theorem fetch_ready (s : MachineState) (pc : s.pc=pcAt 21) (remaining : s.getReg .x11≠0)
    (valid : accessValid (s.getReg .x10) 8=true) (b : Bool) (short : (s.getReg .x11).ult 64=b) :
    pathReady s (fetchWord b) ∧
    let t:=pathEnd s (fetchWord b)
    t.pc=pcAt 27 ∧ t.getReg .x28=s.getMem (s.getReg .x10) ∧ t.getReg .x10=s.getReg .x10+8 ∧
      t.getReg .x31=(if b then s.getReg .x11 else 64) ∧ t.mem=s.mem := by
  change s.regs .x11≠0 at remaining
  change accessValid (s.regs .x10) 8=true at valid
  change (s.regs .x11).ult 64=b at short
  cases b <;> simp +decide [fetchWord,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,instructionCycles,
    execInstrBr,pc,MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,signExtend12,MachineState.getMem,valid,short,remaining] <;> simp_all +decide

end CommitGolfCandidate.Chained.BinaryMachine.Writer
