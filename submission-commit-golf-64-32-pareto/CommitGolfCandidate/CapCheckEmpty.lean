import CommitGolfCandidate.CapCheckLength

/-! Empty requests bypass all leaf and cap work. The actual empty branch
accepts precisely a zero proof length, and both outcomes use real halts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckEmptyState (state : MachineState) : MachineState :=
  state.setPC (if state.getReg .x17 = 0 then 4796 else 4808)

theorem cap_check_empty_tail (state : MachineState) (pc : state.pc = 4140)
    (empty : state.getReg .x27 = 0) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (5 + fuel) state allowCoins =
      pure ⟨if state.getReg .x17 = 0 then .success else .failure,
        capCheckExitState (capCheckEmptyState state) (decide (state.getReg .x17 = 0)),
        5, 0⟩ := by
  let next := state.setPC 4792
  have first : fetch (capProgram.image .check) state =
      some (.base (.BEQ .x27 .x0 652)) := by
    apply cap_image_fetch _ state 11 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.BEQ .x27 .x0 652)) = some next := by
    have emptyRegs : state.regs .x27 = 0 := empty
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, emptyRegs,
      MachineState.getReg, MachineState.setPC, signExtend13, pc, next]
  have second : fetch (capProgram.image .check) next =
      some (.base (.BNE .x17 .x0 16)) := by
    apply cap_image_fetch _ next 174 _ (by decide) rfl
    rfl
  have guarded : ordinaryStep next (.base (.BNE .x17 .x0 16)) =
      some (capCheckEmptyState state) := by
    by_cases zero : state.regs .x17 = 0#64 <;>
      simp [ordinaryStep, memoryArgumentsValid, memAccess,
        execInstrBr, next, MachineState.getReg,
        capCheckEmptyState, signExtend13, MachineState.setPC, zero]
  rw [show 5 + fuel = (4 + fuel) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ first stepped,
    show 4 + fuel = (3 + fuel) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ second guarded]
  by_cases zero : state.getReg .x17 = 0#64
  · have exitPC : (capCheckEmptyState state).pc = 4796 := by
      change (if state.getReg .x17 = 0#64 then 4796 else 4808) = 4796
      simp only [if_pos zero]
    have exit : execute (capProgram.image .check) (3 + fuel)
        (capCheckEmptyState state) allowCoins =
        pure ⟨.success, capCheckExitState (capCheckEmptyState state) true, 3, 0⟩ :=
      cap_check_exit _ true exitPC fuel allowCoins
    rw [exit]
    simp [zero, instructionCycles, Execution.charge]
  · have exitPC : (capCheckEmptyState state).pc = 4808 := by
      change (if state.getReg .x17 = 0#64 then 4796 else 4808) = 4808
      simp only [if_neg zero]
    have exit : execute (capProgram.image .check) (3 + fuel)
        (capCheckEmptyState state) allowCoins =
        pure ⟨.failure, capCheckExitState (capCheckEmptyState state) false, 3, 0⟩ :=
      cap_check_exit _ false exitPC fuel allowCoins
    rw [exit]
    simp [zero, instructionCycles, Execution.charge]

end CommitGolfCandidate
