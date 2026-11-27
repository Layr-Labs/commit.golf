import CommitGolfCandidate.TwoPermutationPackedOpeningExit

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] theorem setup_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] theorem setup_zero (state : MachineState) : state.getReg .x0 = 0 := rfl

def setupInstructions : List Instr :=
  [.ADDI .x20 .x15 0, .ADDI .x21 .x15 0, .BEQ .x16 .x0 2644] ++
    Opening.setupInstructions.drop 3

def setupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (setupInstructions.take count).foldl execInstrBr state

/-- The leader's first twelve setup words; word 12 is now `jal zero,<pre-pass>` (`C3POpenPrepass`). -/
theorem execute_setup12 (state : MachineState) (pc : state.pc = 0x1000)
    (fuel : Nat) (allowCoins : Bool) (nonempty : state.getReg .x16 ≠ 0#64) :
    execute openingImage (12 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (setupPrefix state 12) allowCoins
          return result.charge 12 0) := by
  apply execute_unit_steps (states := setupPrefix state)
  intro i bounded
  refine ⟨.base ((setupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ i _ (by omega)
    · interval_cases i <;>
        simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem setup_pc12 (state : MachineState) (pc : state.pc = 0x1000)
    (nonempty : state.getReg .x16 ≠ 0#64) :
    (setupPrefix state 12).pc = 0x1030 := by
  simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]

theorem setup_registers (state : MachineState) :
    let after := setupPrefix state 13
    after.getReg .x20 = state.getReg .x15 ∧
    after.getReg .x21 = state.getReg .x15 ∧
    after.getReg .x8 = state.getReg .x13 ∧
    after.getReg .x9 = state.getReg .x12 ∧
    after.getReg .x18 = state.getReg .x16 ∧
    after.getReg .x19 = BitVec.ofNat 64 LENGTH ∧
    after.getReg .x22 = state.getReg .x12 + BitVec.ofNat 64 (80 * LENGTH) ∧
    after.getReg .x23 = 1 ∧ after.getReg .x25 = state.getReg .x12 ∧
    after.getReg .x26 = BitVec.ofNat 64 Opening.markBase ∧ after.getReg .x27 = 256 ∧
    after.mem = state.mem := by
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend12, LENGTH,
      LOG_LENGTH, Opening.markBase, beq_iff_eq, empty] <;> rfl

theorem setup_pc (state : MachineState) (pc : state.pc = 0x1000)
    (nonempty : state.getReg .x16 ≠ 0#64) :
    (setupPrefix state 13).pc = 0x1034 := by
  simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]

/-- The zero-cardinality opener bypasses the marks and outputs zero proof bytes. -/
theorem execute_empty (state : MachineState) (pc : state.pc = 0x1000) (fuel : Nat)
    (allowCoins : Bool) (empty : state.getReg .x16 = 0#64) :
    execute openingImage (4 + fuel) state allowCoins =
      (do let out ← execute openingImage fuel (exitPrefix (setupPrefix state 3) 1) allowCoins;return out.charge 4 0) := by
  have ranSetup : execute openingImage (3 + (1 + fuel)) state allowCoins =
      (do let result ← execute openingImage (1 + fuel) (setupPrefix state 3) allowCoins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := setupPrefix state)
    intro i bounded
    refine ⟨.base ((setupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply packed_fetch_base _ i _ (by omega)
      · interval_cases i <;> simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, pc]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have branchPC : (setupPrefix state 3).pc = 0x1a5c := by
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend13, pc, beq_iff_eq, empty]
  rw [show 4 + fuel = 3 + (1 + fuel) by omega, ranSetup, execute_exit _ branchPC]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc]

theorem empty_proof_length (state : MachineState) :
    (exitPrefix (setupPrefix state 3) 1).getReg .x11 = 0 := by
  rw [exit_register]
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend12, beq_iff_eq, empty]

end TwoPermutationPrototype.PackedOpening
