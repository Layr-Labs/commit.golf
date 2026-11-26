import CommitGolfCandidate.TruncSteps
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 7000
set_option maxHeartbeats 90000

private theorem selectExit (s : MachineState) (pc : s.pc=loc 991) :
    Runs (submission.image .check) s (s.setPC (if s.getReg .x19=0 then loc 64 else loc 992)) 1 1 := by
  apply one 991 _ _ (.BEQ .x19 .x0 4484) (by decide) pc (by rfl) _ rfl
  by_cases h : s.getReg .x19=0#64 <;>
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,h,show s.getReg .x0=0#64 from rfl,loc,signExtend13]

theorem normalExit (s : MachineState) (pc : s.pc=loc 281) (mode : s.getReg .x19=0) :
    Runs (submission.image .check) s (s.setPC (loc 64)) 2 2 := by
  have j:=jumpAt (submission.image .check) s 281 991 2840 (by decide) pc (by rfl) (by decide)
  have b:=selectExit (s.setPC (loc 991)) rfl
  rw [MachineState.getReg_setPC,if_pos mode] at b
  exact chain j b

theorem bucketEnter (s : MachineState) (pc : s.pc=loc 281) (mode : s.getReg .x19≠0) :
    Runs (submission.image .check) s (execInstrBr s (.ADDI .x22 .x0 6)) 4 4 := by
  have j:=jumpAt (submission.image .check) s 281 991 2840 (by decide) pc (by rfl) (by decide)
  have b:=selectExit (s.setPC (loc 991)) rfl
  rw [MachineState.getReg_setPC,if_neg mode] at b
  let t:=(s.setReg .x22 6).setPC (loc 993)
  have d : Runs (submission.image .check) ((s.setPC (loc 991)).setPC (loc 992)) t 1 1 := by
    apply one 992 _ _ (.ADDI .x22 .x0 6) (by decide) rfl (by rfl) _ rfl;rfl
  have last:=jumpAt (submission.image .check) t 993 282 2094308 (by decide) rfl (by rfl) (by decide)
  have same : execInstrBr s (.ADDI .x22 .x0 6)=t.setPC (loc 282) := by
    simp only [execInstrBr,show s.getReg .x0=0#64 from rfl,pc];rfl
  rw [same];exact chain (chain (chain j b) d) last
end CommitGolfCandidate.Trunc
