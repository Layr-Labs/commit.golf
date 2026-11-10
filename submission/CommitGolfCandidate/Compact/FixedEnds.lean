import CommitGolfCandidate.Compact.FixedImage
/-! Checked outer-loop and return instructions at their relocated addresses.
These transitions preserve the reference registers and memory. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixedNextState (s : MachineState) : MachineState :=
  (openingNextState s).setPC (if s.getReg .x27-1=0 then 5400 else 4176)

theorem fixed_next (s : MachineState) (pc : s.pc=5388) (fuel : Nat) (coins : Bool) :
    execute fixedImage (3+fuel) s coins=
      (do let result ← execute fixedImage fuel (fixedNextState s) coins
          return result.charge 3 0) := by
  let advanced := (s.setReg .x24 (s.getReg .x24+8)).setPC 5392
  let next := (advanced.setReg .x27 (s.getReg .x27-1)).setPC 5396
  have f0 : fetch fixedImage s=some (.base (.ADDI .x24 .x24 8)) := by
    apply fixed_fetch s 323 _ (by decide) pc;rfl
  have f1 : fetch fixedImage advanced=some (.base (.ADDI .x27 .x27 4095)) := by
    apply fixed_fetch advanced 324 _ (by decide) rfl;rfl
  have f2 : fetch fixedImage next=some (.base (.BNE .x27 .x0 6972)) := by
    apply fixed_fetch next 325 _ (by decide) rfl;rfl
  have step0 : ordinaryStep s (.base (.ADDI .x24 .x24 8))=some advanced := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,advanced,pc]
  have step1 : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095))=some next := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
      advanced,next,BitVec.sub_eq_add_neg,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  have step2 : ordinaryStep next (.base (.BNE .x27 .x0 6972))=some (fixedNextState s) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,
      advanced,next,fixedNextState,openingNextState,BitVec.sub_eq_add_neg,
      MachineState.getReg,MachineState.setReg,MachineState.setPC]
    split <;> simp_all
  rw [show 3+fuel=(fuel+1)+1+1 by omega,
    execute_ordinary_step fixedImage _ _ _ _ _ f0 step0,
    execute_ordinary_step fixedImage _ _ _ _ _ f1 step1,
    execute_ordinary_step fixedImage _ _ _ _ _ f2 step2]
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

theorem fixed_next_frame (s : MachineState) (pc : Word) :
    fixedNextState (s.setPC pc)=fixedNextState s := rfl

def fixedExitState (s : MachineState) : MachineState := (openingExitState s).setPC 5412

theorem fixed_exit (s : MachineState) (pc : s.pc=5400) (fuel : Nat) (coins : Bool) :
    execute fixedImage (4+fuel) s coins=pure ⟨.success,fixedExitState s,4,0⟩ := by
  let s1 := (s.setReg .x11 (s.getReg .x25-s.getReg .x15)).setPC 5404
  let s2 := ((s.setReg .x11 (s.getReg .x25-s.getReg .x15)).setReg .x5 1).setPC 5408
  let s3 := fixedExitState s
  have f0 : fetch fixedImage s=some (.base (.SUB .x11 .x25 .x15)) := by
    apply fixed_fetch s 326 _ (by decide) pc;rfl
  have f1 : fetch fixedImage s1=some (.base (.ADDI .x5 .x0 1)) := by
    apply fixed_fetch s1 327 _ (by decide) rfl;rfl
  have f2 : fetch fixedImage s2=some (.base (.ADDI .x10 .x0 0)) := by
    apply fixed_fetch s2 328 _ (by decide) rfl;rfl
  have f3 : fetch fixedImage s3=some (.base .ECALL) := by
    apply fixed_fetch s3 329 _ (by decide) rfl;rfl
  have step0 : ordinaryStep s (.base (.SUB .x11 .x25 .x15))=some s1 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s1,pc]
  have step1 : ordinaryStep s1 (.base (.ADDI .x5 .x0 1))=some s2 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s1,s2,signExtend12,
      MachineState.setReg,MachineState.getReg,MachineState.setPC]
  have step2 : ordinaryStep s2 (.base (.ADDI .x10 .x0 0))=some s3 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s2,s3,fixedExitState,
      openingExitState,signExtend12,MachineState.setReg,MachineState.getReg,MachineState.setPC]
  have halt : execute fixedImage (fuel+1) s3 coins=pure ⟨.success,s3,1,0⟩ := by
    rw [execute,f3]
    have selector : s3.getReg .x5=1 := rfl
    have succeeded : s3.getReg .x10=0 := rfl
    simp only [selector,succeeded]
    rfl
  rw [show 4+fuel=(fuel+1)+1+1+1 by omega,
    execute_ordinary_step fixedImage _ _ _ _ _ f0 step0,
    execute_ordinary_step fixedImage _ _ _ _ _ f1 step1,
    execute_ordinary_step fixedImage _ _ _ _ _ f2 step2,halt]
  simp [Execution.charge,instructionCycles,s3]
end CommitGolfCandidate.Compact
