import CommitGolfCandidate.ChainedContinuationMask

/-! Native domain preparation leaves the full 256-bit chaining value intact. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem header_execution (image : Image) (base : Word) (code : ContinuationAt image base)
    (s : MachineState) (pc : s.pc = base+4)
    (v32 : accessValid (s.getReg .x10+32) 8 = true)
    (v40 : accessValid (s.getReg .x10+40) 8 = true)
    (v48 : accessValid (s.getReg .x10+48) 8 = true)
    (v56 : accessValid (s.getReg .x10+56) 8 = true) (fuel : Nat) (coins : Bool) :
    execute image (8+fuel) s coins =
      (do let result ← execute image fuel (ordinaryPrefix s 1 8) coins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := ordinaryPrefix s 1)
  intro i inside
  refine ⟨.base (continuationOp (1+i)),?_,?_,?_⟩
  · apply code ⟨1+i,by omega⟩
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,pc,BitVec.add_assoc]
  · have r32 : accessValid (s.regs .x10+32) 8 = true := v32
    have r40 : accessValid (s.regs .x10+40) 8 = true := v40
    have r48 : accessValid (s.regs .x10+48) 8 = true := v48
    have r56 : accessValid (s.regs .x10+56) 8 = true := v56
    interval_cases i <;>
      simp [ordinaryPrefix,continuationOps,continuationOp,ordinaryStep,memoryArgumentsValid,memAccess,
        execInstrBr,MachineState.setPC,MachineState.getReg,MachineState.setReg,MachineState.setMem]
    all_goals first | exact r32 | exact r40 | exact r48 | exact r56
  · interval_cases i <;> rfl

theorem header_pc (s : MachineState) : (ordinaryPrefix s 1 8).pc = s.pc+32 := by
  simp [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem header_register (s : MachineState) (reg : Reg) (not29 : reg ≠ .x29) (not30 : reg ≠ .x30) :
    (ordinaryPrefix s 1 8).getReg reg = s.getReg reg := by
  cases reg <;>
    simp_all [ordinaryPrefix,continuationOps,execInstrBr,MachineState.setPC,MachineState.getReg,
      MachineState.setReg,MachineState.setMem]

end CommitGolfCandidate.Chained.Native
