import CommitGolfCandidate.CapCheckCompression
import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CapExperimentalABI

/-! Actual lower-path orientation branch in the cap checker. The index low
bit selects the same left/right order as the retained compression model;
the fetched instructions and PCs belong solely to the experimental image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckPathBranchState (state : MachineState) : MachineState :=
  (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC
    (if state.getReg .x20 &&& 1 = 0 then 4348 else 4280)

theorem cap_check_path_branch_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x7) :
    (capCheckPathBranchState state).getReg reg = state.getReg reg := by
  simp only [capCheckPathBranchState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_check_path_branch_memory (state : MachineState) :
    (capCheckPathBranchState state).mem = state.mem := rfl

theorem cap_check_path_branch_execute (state : MachineState) (pc : state.pc = 4272)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (2+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckPathBranchState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC 4276
  have first : fetch ((capExperimental 24).image .check) state =
      some (.base (.ANDI .x7 .x20 1)) := by
    apply cap_image_fetch _ state 44 _ (by decide) pc
    rfl
  have second : fetch ((capExperimental 24).image .check) next =
      some (.base (.BEQ .x7 .x0 72)) := by
    apply cap_image_fetch _ next 45 _ (by decide) rfl
    rfl
  have firstStep : ordinaryStep state (.base (.ANDI .x7 .x20 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc]
  have secondStep : ordinaryStep next (.base (.BEQ .x7 .x0 72)) =
      some (capCheckPathBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, capCheckPathBranchState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, first, firstStep, second, secondStep,
    instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem cap_check_path_jump_execute (state : MachineState) (pc : state.pc = 4344)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (state.setPC 4380) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch ((capExperimental 24).image .check) state =
      some (.base (.JAL .x0 36)) := by
    apply cap_image_fetch _ state 62 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 36)) =
      some (state.setPC 4380) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end CommitGolfCandidate
