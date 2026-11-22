import CommitGolfCandidate.GroupOpenExit

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] theorem setup_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] theorem setup_zero (state : MachineState) : state.getReg .x0 = 0 := rfl

def setupInstructions : List Instr :=
  [.ADDI .x20 .x15 0, .ADDI .x21 .x15 0, .BEQ .x16 .x0 2828,
   .ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .LUI .x18 2,
   .LUI .x19 1024, .LUI .x6 131072, .ADD .x24 .x9 .x6, .SLLI .x6 .x6 3, .ADD .x22 .x24 .x6,
   .ADDI .x23 .x0 1, .SLLI .x25 .x16 3, .LUI .x26 1, .ADDI .x27 .x0 256]

def setupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (setupInstructions.take count).foldl execInstrBr state

theorem setup_registers (state : MachineState) :
    let after := setupPrefix state 15
    after.getReg .x20 = state.getReg .x15 ∧
    after.getReg .x21 = state.getReg .x15 ∧
    after.getReg .x8 = state.getReg .x13 ∧
    after.getReg .x9 = state.getReg .x12 ∧
    after.getReg .x18 = 8192 ∧
    after.getReg .x19 = BitVec.ofNat 64 (LENGTH/4) ∧
    after.getReg .x22 = state.getReg .x12 + BitVec.ofNat 64 (288 * LENGTH) ∧
    after.getReg .x24 = state.getReg .x12 + BitVec.ofNat 64 (32*LENGTH) ∧
    after.getReg .x23 = 1 ∧ after.getReg .x25 = state.getReg .x16 <<< (3:Nat) ∧
    after.getReg .x26 = BitVec.ofNat 64 Opening.markBase ∧ after.getReg .x27 = 256 ∧
    after.mem = state.mem := by
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [setupPrefix, setupInstructions, execInstrBr, signExtend12, LENGTH,
      LOG_LENGTH, BitVec.add_assoc, Opening.markBase, beq_iff_eq, empty] <;> rfl

theorem setup_pc (state : MachineState) (pc : state.pc = 0x1000)
    (nonempty : state.getReg .x16 ≠ 0#64) :
    (setupPrefix state 15).pc = 0x103c := by
  simp [setupPrefix, setupInstructions, execInstrBr, pc, beq_iff_eq, nonempty]

/-- The delivered entry rows 0..3: word 2 branches to the header at 713 for a nonempty opening (it stands for
the entry test at index 2 of `setupInstructions`), word 3 jumps to the exit block at 709. -/
def emptyInstructions : List Instr :=
  [.ADDI .x20 .x15 0, .ADDI .x21 .x15 0, .BNE .x16 .x0 2844, .JAL .x0 2824]

def emptyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (emptyInstructions.take count).foldl execInstrBr state

/-- The zero-cardinality opener bypasses the marks and outputs zero proof bytes. -/
theorem execute_empty (state : MachineState) (pc : state.pc = 0x1000) (fuel : Nat)
    (allowCoins : Bool) (empty : state.getReg .x16 = 0#64) :
    execute openingImage (8 + fuel) state allowCoins =
      pure ⟨.success, exitPrefix (emptyPrefix state 4) 3, 8, 0⟩ := by
  have ranSetup : execute openingImage (4 + (4 + fuel)) state allowCoins =
      (do let result ← execute openingImage (4 + fuel) (emptyPrefix state 4) allowCoins
          return result.charge 4 0) := by
    apply execute_unit_steps (states := emptyPrefix state)
    intro i bounded
    refine ⟨.base ((emptyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply packed_fetch_base _ i _ (by omega)
      · interval_cases i <;> simp [emptyPrefix, emptyInstructions, execInstrBr, pc, beq_iff_eq, empty]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have branchPC : (emptyPrefix state 4).pc = 0x1b14 := by
    simp [emptyPrefix, emptyInstructions, execInstrBr, signExtend13, signExtend21, pc, beq_iff_eq, empty]
  rw [show 8 + fuel = 4 + (4 + fuel) by omega, ranSetup, execute_exit _ branchPC]
  simp [Execution.charge]

theorem empty_proof_length (state : MachineState) :
    (exitPrefix (emptyPrefix state 4) 3).getReg .x11 = 0 := by
  rw [exit_register]
  by_cases empty : state.getReg .x16 = 0#64 <;>
    simp [emptyPrefix, emptyInstructions, execInstrBr, signExtend12, beq_iff_eq, empty]

end TwoPermutationPrototype.GroupedOpening
