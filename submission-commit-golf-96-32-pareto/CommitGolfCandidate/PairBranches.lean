import CommitGolfCandidate.PairFinish
import CommitGolfCandidate.PairBatchSteps
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 5100

theorem branch307Yes (o : Oracle) (s : MachineState) (pc : s.pc=5424)
    (flag : s.getReg .x6 = 0#64) :
    Runs o s (s.setPC 5472) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge332 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]
  rfl

theorem branch307No (o : Oracle) (s : MachineState) (pc : s.pc=5424)
    (flag : s.getReg .x6 ≠ 0#64) :
    Runs o s (s.setPC 5428) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge332 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]
  rfl

theorem branch308Yes (o : Oracle) (s : MachineState) (pc : s.pc=5428)
    (flag : s.getReg .x7 = 0#64) :
    Runs o s (s.setPC 5436) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge333 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]
  rfl

theorem branch308No (o : Oracle) (s : MachineState) (pc : s.pc=5428)
    (flag : s.getReg .x7 ≠ 0#64) :
    Runs o s (s.setPC 5432) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge333 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]
  rfl

theorem branch319Yes (o : Oracle) (s : MachineState) (pc : s.pc=5472)
    (flag : s.getReg .x7 = 0#64) :
    Runs o s (s.setPC 5536) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge344 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_pos flag,pc]
  rfl

theorem branch319No (o : Oracle) (s : MachineState) (pc : s.pc=5472)
    (flag : s.getReg .x7 ≠ 0#64) :
    Runs o s (s.setPC 5476) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel; rw [Nat.add_comm 1 fuel,edge344 s pc]
  have x0 : s.getReg .x0 = 0#64 := rfl
  simp only [execInstrBr,x0,beq_iff_eq,if_neg flag,pc]
  rfl

theorem jump309 (o : Oracle) (s : MachineState) (pc : s.pc=5432) :
    Runs o s (s.setPC 5508) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel;rw [Nat.add_comm 1 fuel,edge334 s pc]
  simp only [execInstrBr,MachineState.setReg,pc];rfl

theorem jump318 (o : Oracle) (s : MachineState) (pc : s.pc=5468) :
    Runs o s (s.setPC 5508) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel;rw [Nat.add_comm 1 fuel,edge343 s pc]
  simp only [execInstrBr,MachineState.setReg,pc];rfl

theorem jump334 (o : Oracle) (s : MachineState) (pc : s.pc=5532) :
    Runs o s (s.setPC 5568) 1 0 := by
  apply pureBlockRuns (cyc:=1)
  intro fuel;rw [Nat.add_comm 1 fuel,edge359 s pc]
  simp only [execInstrBr,MachineState.setReg,pc];rfl
end CommitGolfCandidate.PairCap.Batch
