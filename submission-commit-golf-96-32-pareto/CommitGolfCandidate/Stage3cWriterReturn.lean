import CommitGolfCandidate.Stage3cWriterCode
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 80000
theorem finished (s : MachineState) (pc : s.pc=pcAt 21) (zero : s.getReg .x11=0) :
    pathReady s finish ∧ (pathEnd s finish).pc=(s.getReg .x1 &&& ~~~1#64) ∧
    (pathEnd s finish).mem=s.mem ∧ (pathEnd s finish).regs=s.regs := by
  change s.regs .x11=0 at zero
  simp +decide [finish,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,instructionCycles,
    execInstrBr,pc,zero,MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,signExtend12]
end CommitGolfCandidate.Chained.BinaryMachine.Writer
