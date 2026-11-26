import CommitGolfCandidate.TruncNormalCompare
import CommitGolfCandidate.CheckLoop
import CommitGolfCandidate.TruncRecordExit
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 100000

theorem check_target (state : MachineState) (pc : state.pc = 4352)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (2 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (checkTargetState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x7 (state.getReg .x20 <<< 5)).setPC 4356
  have f0 : fetch (Trunc.wireImage true) state = some (.base (.SLLI .x7 .x20 5)) := by
    apply fetchAt _ _ 64 _ (by decide) pc; rfl
  have f1 : fetch (Trunc.wireImage true) s1 = some (.base (.ADD .x23 .x26 .x7)) := by
    apply fetchAt _ _ 65 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.SLLI .x7 .x20 5)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADD .x23 .x26 .x7)) = some (checkTargetState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, checkTargetState,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The machine-state distribution at the digest comparison (PC 4360) for one position
at path depth `pathDepth` (`24` or `17`). -/
theorem check_position_next (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (3 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (checkPositionNextState state) allowCoins
          return result.charge 3 0) := by
  let next := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4412
  let decremented := (next.setReg .x27 (state.getReg .x27 - 1)).setPC 4416
  have f0 : fetch (Trunc.wireImage true) state = some (.base (.ADDI .x24 .x24 8)) := by
    apply fetchAt _ _ 78 _ (by decide) pc; rfl
  have f1 : fetch (Trunc.wireImage true) next = some (.base (.ADDI .x27 .x27 4095)) := by
    apply fetchAt _ _ 79 _ (by decide) rfl; rfl
  have f2 : fetch (Trunc.wireImage true) decremented = some (.base (.BNE .x27 .x0 7932)) := by
    apply fetchAt _ _ 80 _ (by decide) rfl; rfl
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


theorem recordStart (s : MachineState) (pc : s.pc=loc 15) :
    Runs (Trunc.wireImage true) s (s.setPC (loc 207)) 1 1 :=
  jumpAt _ s 15 207 768 (by decide) pc (by rfl) (by decide)
end CommitGolfCandidate.Trunc.Normal
