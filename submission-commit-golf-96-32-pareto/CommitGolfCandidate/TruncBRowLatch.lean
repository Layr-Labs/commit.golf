import CommitGolfCandidate.TruncBFoldFinish
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 40000

attribute [local irreducible] nextEdge
theorem latchRegEq (s : MachineState) (r : Reg) : (nextEdge s).getReg r=(recordNextState s).getReg r := by
  simp only [MachineState.getReg,latchRegs s]

theorem latchKept (s : MachineState) (r : Reg) (h : r∈[Reg.x8,.x25,.x21,.x30,.x19,.x26]) :
    (nextEdge s).getReg r=s.getReg r := by
  rw [latchRegEq s r]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem latchIp (s : MachineState) :
    (nextEdge s).getReg .x24=s.getReg .x24+8#64 :=
  (latchRegEq s .x24).trans (latchValues s).2

theorem latchRem (s : MachineState) :
    (nextEdge s).getReg .x27=s.getReg .x27+signExtend12 4095 :=
  (latchRegEq s .x27).trans (latchValues s).1

end CommitGolfCandidate.Trunc.Batch
