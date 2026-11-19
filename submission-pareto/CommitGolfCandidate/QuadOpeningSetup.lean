import CommitGolfCandidate.QuadOpeningExit

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] QOpening.getReg_setReg QOpening.getReg_setMem

@[local simp] theorem setup_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] theorem setup_zero (state : MachineState) : state.getReg .x0 = 0 := rfl

def setupInstructions : List Instr :=
  [.ADDI .x20 .x15 0, .ADDI .x21 .x15 0, .BEQ .x16 .x0 3068,
   .ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .ADDI .x18 .x16 0,
   .LUI .x19 4096, .LUI .x22 442369, .ADD .x22 .x9 .x22, .LUI .x24 65537, .ADD .x24 .x9 .x24,
   .ADDI .x23 .x0 1, .ADDI .x25 .x9 0, .LUI .x26 1, .ADDI .x27 .x0 256,
   .LUI .x28 413700, .ADD .x28 .x9 .x28]

def setupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (setupInstructions.take count).foldl execInstrBr state

theorem execute_setup (state : MachineState) (pc : state.pc = 0x1000)
    (fuel : Nat) (allowCoins : Bool) (nonempty : state.getReg .x16 ≠ 0#64) :
    execute openingImage (17 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (setupPrefix state 17) allowCoins
          return result.charge 17 0) := by
  apply execute_unit_steps (states := setupPrefix state)
  intro i bounded
  refine ⟨.base ((setupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ i _ (by omega)
    · interval_cases i <;>
        simp [setupPrefix, setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem setup_registers (state : MachineState) :
    let after := setupPrefix state 17
    after.getReg .x20 = state.getReg .x15 ∧
    after.getReg .x21 = state.getReg .x15 ∧
    after.getReg .x8 = state.getReg .x13 ∧
    after.getReg .x9 = state.getReg .x12 ∧
    after.getReg .x18 = state.getReg .x16 ∧
    after.getReg .x19 = BitVec.ofNat 64 LENGTH ∧
    after.getReg .x22 = state.getReg .x12 + BitVec.ofNat 64 0x6C001000 ∧
    after.getReg .x24 = state.getReg .x12 + BitVec.ofNat 64 0x10001000 ∧
    after.getReg .x23 = 1 ∧ after.getReg .x25 = state.getReg .x12 ∧
    after.getReg .x26 = BitVec.ofNat 64 QOpening.markBase ∧ after.getReg .x27 = 256 ∧
    after.getReg .x28 = state.getReg .x12 + BitVec.ofNat 64 0x65004000 ∧
    after.mem = state.mem := by
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [setupPrefix, setupInstructions, execInstrBr, signExtend12, LENGTH,
      LOG_LENGTH, QOpening.markBase, beq_iff_eq, empty] <;> rfl

theorem setup_pc (state : MachineState) (pc : state.pc = 0x1000)
    (nonempty : state.getReg .x16 ≠ 0#64) :
    (setupPrefix state 17).pc = 0x1044 := by
  simp [setupPrefix, setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]

/-- The zero-cardinality opener bypasses the marks and outputs zero proof bytes. -/
theorem execute_empty (state : MachineState) (pc : state.pc = 0x1000) (fuel : Nat)
    (allowCoins : Bool) (empty : state.getReg .x16 = 0#64) :
    execute openingImage (7 + fuel) state allowCoins =
      pure ⟨.success, exitPrefix (setupPrefix state 3) 3, 7, 0⟩ := by
  have ranSetup : execute openingImage (3 + (4 + fuel)) state allowCoins =
      (do let result ← execute openingImage (4 + fuel) (setupPrefix state 3) allowCoins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := setupPrefix state)
    intro i bounded
    refine ⟨.base ((setupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply packed_fetch_base _ i _ (by omega)
      · interval_cases i <;> simp [setupPrefix, setupInstructions, execInstrBr, pc]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have branchPC : (setupPrefix state 3).pc = 0x1c04 := by
    simp [setupPrefix, setupInstructions, execInstrBr, signExtend13, pc, beq_iff_eq, empty]
  rw [show 7 + fuel = 3 + (4 + fuel) by omega, ranSetup, execute_exit _ branchPC]
  simp [Execution.charge]

theorem empty_proof_length (state : MachineState) :
    (exitPrefix (setupPrefix state 3) 3).getReg .x11 = 0 := by
  rw [exit_register]
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [setupPrefix, setupInstructions, execInstrBr, signExtend12, beq_iff_eq, empty]

end TwoPermutationPrototype.QuadOpening
