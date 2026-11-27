import CommitGolfCandidate.Stage3cWriterCode
namespace CommitGolfCandidate.Chained.BinaryMachine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 80000
def buffered (s : MachineState) := s.getReg .x23 ||| (s.getReg .x28 <<< ((s.getReg .x24).toNat%64))
def occupied (s : MachineState) := s.getReg .x24+s.getReg .x31

theorem mix_ready (s : MachineState) (pc : s.pc=pcAt 27) (threshold : s.getReg .x27=64) :
    pathReady s mix ∧
    let t:=pathEnd s mix
    t.pc=pcAt (if (occupied s).ult 64 then 21 else 32) ∧ t.getReg .x11=s.getReg .x11-s.getReg .x31 ∧
    t.getReg .x23=buffered s ∧ t.getReg .x24=occupied s ∧ t.mem=s.mem := by
  change s.regs .x27=64 at threshold
  by_cases small : (occupied s).ult 64 = true <;>
    simp +decide [mix,pathReady,pathEnd,buffered,occupied,ordinaryStep,memoryArgumentsValid,memAccess,instructionCycles,
      execInstrBr,pc,MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,threshold] at * <;> simp_all +decide

end CommitGolfCandidate.Chained.BinaryMachine.Writer
