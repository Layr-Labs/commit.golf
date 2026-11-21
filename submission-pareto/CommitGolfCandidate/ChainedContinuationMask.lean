import CommitGolfCandidate.ChainedContinuationCode

/-! The continuation fragment masks once, after its last full-width reply. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

theorem mask_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+60)
    (valid : accessValid (s.getReg .x10+24) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins =
      (do let result ← execute image fuel (ordinaryPrefix s 15 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := ordinaryPrefix s 15)
  intro i inside
  refine ⟨.base (continuationOp (15+i)),?_,?_,?_⟩
  · apply code ⟨15+i,by omega⟩
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,pc,BitVec.add_assoc]
  · have rawValid : accessValid (s.regs .x10+24) 8 = true := valid
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,continuationOp,ordinaryStep,memoryArgumentsValid,memAccess,
        execInstrBr,MachineState.setPC,MachineState.getReg,MachineState.setReg,MachineState.setMem]
    all_goals exact rawValid
  · interval_cases i <;> rfl

theorem empty_continuation_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base) (empty : s.getReg .x18 = 0)
    (valid : accessValid (s.getReg .x10+24) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (5+fuel) s coins =
      (do let result ← execute image fuel (ordinaryPrefix (s.setPC (base+60)) 15 4) coins
          return result.charge 5 0) := by
  have fetched : fetch image s = some (.base (.BEQ .x18 .x0 60)) := by
    apply code ⟨0,by decide⟩
    simpa using pc
  have step : ordinaryStep s (.base (.BEQ .x18 .x0 60)) = some (s.setPC (base+60)) := by
    have rawEmpty : s.regs .x18 = 0 := empty
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,rawEmpty,MachineState.getReg,pc]
    rfl
  rw [show 5+fuel = (4+fuel)+1 by omega,
    execute_ordinary_step image _ _ _ _ coins fetched step]
  rw [mask_execution image base code (s.setPC (base+60)) rfl valid fuel coins]
  simp [Execution.charge,instructionCycles,← Nat.add_assoc]

theorem mask_invalid_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+60)
    (invalid : accessValid (s.getReg .x10+24) 8 = false) (fuel : Nat) (coins : Bool) :
    execute image (fuel+1) s coins = pure ⟨.failure,s,1,0⟩ := by
  have fetched : fetch image s = some (.base (.LD .x29 .x10 24)) := code ⟨15,by decide⟩ s pc
  have step : ordinaryStep s (.base (.LD .x29 .x10 24)) = none := by
    change (if accessValid (s.getReg .x10+24) 8 then some _ else none) = none
    rw [invalid]
    rfl
  simp only [execute,fetched,step]

end CommitGolfCandidate.Chained.Native
