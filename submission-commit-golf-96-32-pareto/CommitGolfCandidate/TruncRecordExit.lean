import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 7000
set_option maxHeartbeats 90000

private theorem selectExit (s : MachineState) (pc : s.pc=loc 1023) :
    Runs (Trunc.wireImage true) s (s.setPC (if s.getReg .x19=0 then loc 64 else loc 1024)) 1 1 := by
  apply one 1023 _ _ (.BEQ .x19 .x0 4356) (by decide) pc (by rfl) _ rfl
  by_cases h : s.getReg .x19=0#64 <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,h,show s.getReg .x0=0#64 from rfl,loc,signExtend13]

theorem normalExit (s : MachineState) (pc : s.pc=loc 256) (mode : s.getReg .x19=0) :
    Runs (Trunc.wireImage true) s (s.setPC (loc 64)) 2 2 := by
  have j:=jumpAt (Trunc.wireImage true) s 256 1023 3068 (by decide) pc (by rfl) (by decide)
  have b:=selectExit (s.setPC (loc 1023)) rfl
  rw [MachineState.getReg_setPC,if_pos mode] at b
  exact chain j b

theorem bucketEnter (s : MachineState) (pc : s.pc=loc 256) (mode : s.getReg .x19≠0) :
    Runs (Trunc.wireImage true) s (execInstrBr s (.ADDI .x22 .x0 6)) 4 4 := by
  have j:=jumpAt (Trunc.wireImage true) s 256 1023 3068 (by decide) pc (by rfl) (by decide)
  have b:=selectExit (s.setPC (loc 1023)) rfl
  rw [MachineState.getReg_setPC,if_neg mode] at b
  let t:=(s.setReg .x22 6).setPC (loc 1025)
  have d : Runs (Trunc.wireImage true) ((s.setPC (loc 1023)).setPC (loc 1024)) t 1 1 := by
    apply one 1024 _ _ (.ADDI .x22 .x0 6) (by decide) rfl (by rfl) _ rfl;rfl
  have last:=jumpAt (Trunc.wireImage true) t 1025 257 2094080 (by decide) rfl (by rfl) (by decide)
  have same : execInstrBr s (.ADDI .x22 .x0 6)=t.setPC (loc 257) := by
    simp only [execInstrBr,show s.getReg .x0=0#64 from rfl,pc];rfl
  rw [same];exact chain (chain (chain j b) d) last
end CommitGolfCandidate.Trunc
