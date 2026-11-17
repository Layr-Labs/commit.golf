import CommitGolfCandidate.Compact.FastOpeningImage
/-! Checked outer-loop and return instructions at their relocated addresses.
These transitions preserve the reference registers and memory. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fastNextState (s : MachineState) : MachineState :=
  (openingNextState s).setPC (if s.getReg .x27-1=0 then 5604 else 4176)

theorem fast_next (s : MachineState) (pc : s.pc=5592) (fuel : Nat) (coins : Bool) :
    execute fastImage (3+fuel) s coins=
      (do let result ← execute fastImage fuel (fastNextState s) coins
          return result.charge 3 0) := by
  let advanced := (s.setReg .x24 (s.getReg .x24+8)).setPC 5596
  let next := (advanced.setReg .x27 (s.getReg .x27-1)).setPC 5600
  have f0 : fetch fastImage s=some (.base (.ADDI .x24 .x24 8)) := by
    apply fast_fetch s 374 _ (by decide) pc;rfl
  have f1 : fetch fastImage advanced=some (.base (.ADDI .x27 .x27 4095)) := by
    apply fast_fetch advanced 375 _ (by decide) rfl;rfl
  have f2 : fetch fastImage next=some (.base (.BNE .x27 .x0 6768)) := by
    apply fast_fetch next 376 _ (by decide) rfl;rfl
  have step0 : ordinaryStep s (.base (.ADDI .x24 .x24 8))=some advanced := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,advanced,pc]
  have step1 : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095))=some next := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend12,
      advanced,next,BitVec.sub_eq_add_neg,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  have step2 : ordinaryStep next (.base (.BNE .x27 .x0 6768))=some (fastNextState s) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,
      advanced,next,fastNextState,openingNextState,BitVec.sub_eq_add_neg,
      MachineState.getReg,MachineState.setReg,MachineState.setPC]
    split <;> simp_all
  rw [show 3+fuel=(fuel+1)+1+1 by omega,
    execute_ordinary_step fastImage _ _ _ _ _ f0 step0,
    execute_ordinary_step fastImage _ _ _ _ _ f1 step1,
    execute_ordinary_step fastImage _ _ _ _ _ f2 step2]
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

theorem fast_next_frame (s : MachineState) (pc : Word) :
    fastNextState (s.setPC pc)=fastNextState s := rfl

def fastExitState (s : MachineState) : MachineState := (openingExitState s).setPC 5616

theorem fast_exit (s : MachineState) (pc : s.pc=5604) (fuel : Nat) (coins : Bool) :
    execute fastImage (4+fuel) s coins=pure ⟨.success,fastExitState s,4,0⟩ := by
  let s1 := (s.setReg .x11 (s.getReg .x25-s.getReg .x15)).setPC 5608
  let s2 := ((s.setReg .x11 (s.getReg .x25-s.getReg .x15)).setReg .x5 1).setPC 5612
  let s3 := fastExitState s
  have f0 : fetch fastImage s=some (.base (.SUB .x11 .x25 .x15)) := by
    apply fast_fetch s 377 _ (by decide) pc;rfl
  have f1 : fetch fastImage s1=some (.base (.ADDI .x5 .x0 1)) := by
    apply fast_fetch s1 378 _ (by decide) rfl;rfl
  have f2 : fetch fastImage s2=some (.base (.ADDI .x10 .x0 0)) := by
    apply fast_fetch s2 379 _ (by decide) rfl;rfl
  have f3 : fetch fastImage s3=some (.base .ECALL) := by
    apply fast_fetch s3 380 _ (by decide) rfl;rfl
  have step0 : ordinaryStep s (.base (.SUB .x11 .x25 .x15))=some s1 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s1,pc]
  have step1 : ordinaryStep s1 (.base (.ADDI .x5 .x0 1))=some s2 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s1,s2,signExtend12,
      MachineState.setReg,MachineState.getReg,MachineState.setPC]
  have step2 : ordinaryStep s2 (.base (.ADDI .x10 .x0 0))=some s3 := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,s2,s3,fastExitState,
      openingExitState,signExtend12,MachineState.setReg,MachineState.getReg,MachineState.setPC]
  have halt : execute fastImage (fuel+1) s3 coins=pure ⟨.success,s3,1,0⟩ := by
    rw [execute,f3]
    have selector : s3.getReg .x5=1 := rfl
    have succeeded : s3.getReg .x10=0 := rfl
    simp only [selector,succeeded]
    rfl
  rw [show 4+fuel=(fuel+1)+1+1+1 by omega,
    execute_ordinary_step fastImage _ _ _ _ _ f0 step0,
    execute_ordinary_step fastImage _ _ _ _ _ f1 step1,
    execute_ordinary_step fastImage _ _ _ _ _ f2 step2,halt]
  simp [Execution.charge,instructionCycles,s3]
end CommitGolfCandidate.Compact
