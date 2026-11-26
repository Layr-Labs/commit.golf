import CommitGolfCandidate.LateNormalPath

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

def checkTargetState (state : MachineState) : MachineState :=
  ((state.setReg .x7 (state.getReg .x20 <<< 5)).setReg .x23
    (state.getReg .x26 + (state.getReg .x20 <<< 5))).setPC 4360

theorem check_target (state : MachineState) (pc : state.pc = 4352)
    (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (2 + fuel) state allowCoins =
      (do let result ← execute (checkerImage) fuel (checkTargetState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x7 (state.getReg .x20 <<< 5)).setPC 4356
  have f0 : fetch (checkerImage) state = some (.base (.SLLI .x7 .x20 5)) := by
    apply check_fetch _ 64 _ (by decide) pc; rfl
  have f1 : fetch (checkerImage) s1 = some (.base (.ADD .x23 .x26 .x7)) := by
    apply check_fetch _ 65 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.SLLI .x7 .x20 5)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADD .x23 .x26 .x7)) = some (checkTargetState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, checkTargetState,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def checkPositionNextState (state : MachineState) : MachineState :=
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 (state.getReg .x27 - 1)).setPC
    (if state.getReg .x27 - 1 = 0 then 4420 else 4156)

theorem check_position_next_pc (state : MachineState) :
    (checkPositionNextState state).pc =
      if state.getReg .x27 - 1 = 0 then 4420 else 4156 := rfl

theorem check_position_next_counter (state : MachineState) :
    (checkPositionNextState state).getReg .x27 = state.getReg .x27 - 1 := rfl

theorem check_position_next (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (3 + fuel) state allowCoins =
      (do let result ← execute (checkerImage) fuel (checkPositionNextState state) allowCoins
          return result.charge 3 0) := by
  let next := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4412
  let decremented := (next.setReg .x27 (state.getReg .x27 - 1)).setPC 4416
  have f0 : fetch (checkerImage) state = some (.base (.ADDI .x24 .x24 8)) := by
    apply check_fetch _ 78 _ (by decide) pc; rfl
  have f1 : fetch (checkerImage) next = some (.base (.ADDI .x27 .x27 4095)) := by
    apply check_fetch _ 79 _ (by decide) rfl; rfl
  have f2 : fetch (checkerImage) decremented = some (.base (.BNE .x27 .x0 7932)) := by
    apply check_fetch _ 80 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x27 .x27 4095)) = some decremented := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, decremented, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep decremented (.base (.BNE .x27 .x0 7932)) = some (checkPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      decremented, next, checkPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate.Late.Check.Normal
