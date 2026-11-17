import CommitGolfCandidate.CapCheckLengthControl

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckConstantsInstructions : List Instr :=
  [.ADDI .x21 .x0 0, .SLLI .x21 .x21 11, .ADDI .x21 .x21 256,
   .ADDI .x9 .x0 0, .SLLI .x9 .x9 11, .ADDI .x9 .x9 14,
   .SLLI .x9 .x9 11, .ADDI .x9 .x9 0,
   .ADDI .x18 .x0 0, .SLLI .x18 .x18 11, .ADDI .x18 .x18 6,
   .SLLI .x18 .x18 11, .ADDI .x18 .x18 0,
   .ADDI .x19 .x0 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 256,
   .ADDI .x31 .x0 1]

def capCheckConstantsPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckConstantsInstructions.take count).foldl execInstrBr state

theorem cap_check_constants_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 17) :
    (capCheckConstantsPrefix state count).pc =
      state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckConstantsPrefix, capCheckConstantsInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_constants_execute (state : MachineState)
    (pc : state.pc = 4144) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (17 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckConstantsPrefix state 17) allowCoins
          return result.charge 17 0) := by
  apply execute_unit_steps (states := capCheckConstantsPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckConstantsInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (12 + i) _ (by omega)
    · rw [cap_check_constants_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_constants_registers (state : MachineState) :
    (capCheckConstantsPrefix state 17).getReg .x21 = 256 ∧
    (capCheckConstantsPrefix state 17).getReg .x9 = 28672 ∧
    (capCheckConstantsPrefix state 17).getReg .x18 = 12288 ∧
    (capCheckConstantsPrefix state 17).getReg .x19 = 256 ∧
    (capCheckConstantsPrefix state 17).getReg .x31 = 1 := by
  simp [capCheckConstantsPrefix, capCheckConstantsInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem cap_check_constants_memory (state : MachineState) :
    (capCheckConstantsPrefix state 17).mem = state.mem := rfl

end CommitGolfCandidate
