import CommitGolfCandidate.CapCheckLeafLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

theorem cap_check_leaf_return_execute (state : MachineState) (pc : state.pc = 4892)
    (link : state.getReg .x1 = 4256) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (1 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (state.setPC 4256) allowCoins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) =
      some (state.setPC 4256) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (cap_check_leaf_return_fetched state pc) stepped]
  rfl

theorem cap_check_leaf_subroutine_execute (state : MachineState) (pc : state.pc = 4820)
    (link : state.getReg .x1 = 4256) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (138 + fuel) state allowCoins =
      (do let finished ← capCheckLeafLoop ((state.setReg .x28 8).setPC 4824) 8
          let result ← execute ((capExperimental 24).image .check) fuel (finished.setPC 4256) allowCoins
          return result.charge 194 8) := by
  let initialized := (state.setReg .x28 8).setPC 4824
  have fetched : fetch ((capExperimental 24).image .check) state =
      some (.base (.ADDI .x28 .x0 8)) := by
    exact cap_check_leaf_init_fetched state pc
  have stepped : ordinaryStep state (.base (.ADDI .x28 .x0 8)) = some initialized := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      initialized, pc, MachineState.getReg]
  have initCounter : initialized.getReg .x28 = BitVec.ofNat 64 8 := by
    simp [initialized, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have initScratch : initialized.getReg .x21 = 256 := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (initialized.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using sourceValid
  rw [show 138 + fuel = (17 * 8 + (1 + fuel)) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped,
    cap_check_leaf_loop_execute initialized 8 (by decide) (fun _ => rfl) initCounter initScratch initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := cap_check_leaf_loop_finished initialized 8 (by decide) (fun _ => rfl) initCounter finished reachable
  have finalLink : finished.getReg .x1 = 4256 := by
    rw [done.2.1]
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using link
  rw [cap_check_leaf_return_execute finished (done.2.2 (by decide)) finalLink]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]


end CommitGolfCandidate
