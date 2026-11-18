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

theorem execute_setup (state : MachineState) (pc : state.pc = 0x1000)
    (fuel : Nat) (allowCoins : Bool) (nonempty : state.getReg .x16 ≠ 0#64) :
    execute openingImage (13 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (setupPrefix state 13) allowCoins
          return result.charge 13 0) := by
  apply execute_unit_steps (states := setupPrefix state)
  intro i bounded
  refine ⟨.base ((setupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply packed_fetch_base _ i _ (by omega)
    · interval_cases i <;>
        simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

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

/-- The zero-cardinality opener bypasses the marks; the exit block and the pack postpass then
output zero proof bytes. -/
theorem execute_empty (state : MachineState) (pc : state.pc = 0x1000)
    (empty : state.getReg .x16 = 0#64)
    (start : state.getReg .x15 = BitVec.ofNat 64 Opening.proofBase) :
    ∃ final : MachineState,
      (∀ fuel allowCoins, execute openingImage (3 + Pack.exitSteps 0 0 + fuel) state allowCoins =
        pure ⟨.success, final, 3 + Pack.exitCycles 0 0, 0⟩) ∧
      (final.getReg .x11).toNat = 0 := by
  have ranSetup (fuel : Nat) (allowCoins : Bool) :
      execute openingImage (3 + fuel) state allowCoins =
        (do let result ← execute openingImage fuel (setupPrefix state 3) allowCoins
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
  have count : (setupPrefix state 3).getReg .x16 = BitVec.ofNat 64 0 := by
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, beq_iff_eq, empty]
  have begin : (setupPrefix state 3).getReg .x20 = BitVec.ofNat 64 Opening.proofBase := by
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend12, beq_iff_eq,
      empty, start]
  have length : (setupPrefix state 3).getReg .x21 - (setupPrefix state 3).getReg .x20 =
      BitVec.ofNat 64 (498*0 + 30*0) := by
    simp [setupPrefix, setupInstructions, Opening.setupInstructions, execInstrBr, signExtend12, beq_iff_eq, empty]
  obtain ⟨final, ran, ret, _, _⟩ :=
    execute_exit _ branchPC 0 0 count begin length (by unfold Pack.capacityBytes; omega)
  refine ⟨final, fun fuel allowCoins => ?_, by rw [ret]; rfl⟩
  rw [Nat.add_assoc, ranSetup, ran]
  simp [Execution.charge]

end TwoPermutationPrototype.PackedOpening
