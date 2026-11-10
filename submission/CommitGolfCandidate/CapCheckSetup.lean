import CommitGolfCandidate.CapCheckLeafCall
import CommitGolfCandidate.CapFlow

/-! The real cap checker first retains ABI pointers, computes the proof end,
and compares length with 576 times the requested count. This comparison is
only a lower bound: cap boundary bytes follow the fixed lower records.
The gate executes before any proof-buffer load or oracle query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckSetupInstructions : List Instr :=
  [.ADDI .x26 .x11 0, .ADDI .x24 .x13 0, .ADDI .x8 .x14 0,
   .ADDI .x25 .x15 0, .ADDI .x27 .x16 0, .ADD .x22 .x15 .x17,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 576]

def capCheckSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckSetupInstructions.take count).foldl execInstrBr state

def capCheckMultiplied (state : MachineState) : MachineState :=
  ((capCheckSetupPrefix state 9).setReg .x7 (state.getReg .x16 * 576)).setPC 4136

def capCheckLengthState (state : MachineState) : MachineState :=
  capFlowState (.below .x17 .x7 672) (capCheckMultiplied state)

theorem cap_check_setup_pc (state : MachineState) (count : Nat) (bounded : count ≤ 9) :
    (capCheckSetupPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckSetupPrefix, capCheckSetupInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_setup_execute (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (9 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckSetupPrefix state 9) allowCoins
          return result.charge 9 0) := by
  apply execute_unit_steps (states := capCheckSetupPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ i _ (by omega)
    · rw [cap_check_setup_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_setup_registers (state : MachineState) :
    (capCheckSetupPrefix state 9).getReg .x26 = state.getReg .x11 ∧
    (capCheckSetupPrefix state 9).getReg .x24 = state.getReg .x13 ∧
    (capCheckSetupPrefix state 9).getReg .x8 = state.getReg .x14 ∧
    (capCheckSetupPrefix state 9).getReg .x25 = state.getReg .x15 ∧
    (capCheckSetupPrefix state 9).getReg .x27 = state.getReg .x16 ∧
    (capCheckSetupPrefix state 9).getReg .x22 = state.getReg .x15 + state.getReg .x17 ∧
    (capCheckSetupPrefix state 9).getReg .x6 = 576 ∧
    (capCheckSetupPrefix state 9).getReg .x16 = state.getReg .x16 ∧
    (capCheckSetupPrefix state 9).getReg .x17 = state.getReg .x17 := by
  simp [capCheckSetupPrefix, capCheckSetupInstructions, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem cap_check_length_memory (state : MachineState) :
    (capCheckLengthState state).mem = state.mem := by
  rw [capCheckLengthState, cap_flow_memory]
  rfl

/-- Eleven real instructions, fourteen cycles and no queries to the length decision. -/
theorem cap_check_length_gate (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (11 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckLengthState state) allowCoins
          return result.charge 14 0) := by
  let ready := capCheckSetupPrefix state 9
  have readyPC : ready.pc = 4132 := by
    rw [cap_check_setup_pc state 9 (by decide), pc]
    rfl
  have fetchedMul : fetch ((capExperimental 24).image .check) ready =
      some (.base (.MUL .x7 .x16 .x6)) := by
    apply cap_image_fetch _ ready 9 _ (by decide) readyPC
    rfl
  have fetchedBranch : fetch ((capExperimental 24).image .check) (capCheckMultiplied state) =
      some (.base (.BLTU .x17 .x7 672)) := by
    apply cap_image_fetch _ _ 10 _ (by decide) rfl
    rfl
  have registers := cap_check_setup_registers state
  have stepped : ordinaryStep ready (.base (.MUL .x7 .x16 .x6)) =
      some (capCheckMultiplied state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte,
      execInstrBr, registers.2.2.2.2.2.2.1, registers.2.2.2.2.2.2.2.1, readyPC,
      capCheckMultiplied, ready]
    rfl
  rw [show 11 + fuel = 9 + (2 + fuel) by omega, cap_check_setup_execute state pc,
    show 2 + fuel = (1 + fuel) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetchedMul stepped]
  rw [cap_flow_execute _ (.below .x17 .x7 672) _ fetchedBranch]
  simp [capCheckLengthState, instructionCycles, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
