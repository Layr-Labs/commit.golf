import CommitGolfCandidate.TwoPermutationPackedOpeningCapCursor

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem step_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem step_zeroreg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def advanceCode : List Instr :=
  [.ANDI .x7 .x6 1, .BNE .x7 .x0 20, .ADDI .x6 .x6 1, .JAL .x0 2096980,
   .ADDI .x0 .x0 0, .ADDI .x0 .x0 0, .SRLI .x6 .x6 1, .BNE .x6 .x0 8164]

@[local simp] theorem advance_code : capWalkInstructions.drop 41 = advanceCode := rfl
@[local simp] theorem right_code : capWalkInstructions.drop 43 = advanceCode.drop 2 := rfl
@[local simp] theorem up_code : capWalkInstructions.drop 47 = advanceCode.drop 6 := rfl

def advancePrefix (state : MachineState) (index count : Nat) : MachineState :=
  ((capWalkInstructions.drop index).take count).foldl execInstrBr state

/-- Two adjacent, ordinary cap instructions with no accessed memory. The first
instruction in each such pair follows the straight-line PC. -/
private theorem execute_cap_pair (state : MachineState) (index : Nat) (fuel : Nat)
    (allowCoins : Bool) (bounded : index + 1 < 49)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (626 + index)))
    (firstPC : (advancePrefix state index 1).pc = BitVec.ofNat 64 (4096 + 4 * (626 + (index + 1))))
    (trace : ∀ i < 2,
      (openingImage.code[626 + (index + i)]?).bind Opening.decodeBase =
        some ((capWalkInstructions.drop index)[i]?.getD .EBREAK) ∧
      ordinaryStep (advancePrefix state index i)
        (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) =
          some (advancePrefix state index (i+1)) ∧
      instructionCycles (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) = 1) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state index 2) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := advancePrefix state index)
  intro i hi
  obtain ⟨decodes, steps, cost⟩ := trace i hi
  refine ⟨.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK), ?_, steps, cost⟩
  apply packed_fetch_base _ (626 + (index + i)) _ (by omega) _ decodes
  interval_cases i
  · exact pc
  · exact firstPC

/-- The branch falls through for an even node and jumps for an odd node. -/
theorem execute_advance_parity_test (state : MachineState) (pc : state.pc = 0x1a6c)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 41 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 41 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_parity_target (state : MachineState) (pc : state.pc = 0x1a6c) :
    (advancePrefix state 41 2).pc =
      if (state.getReg .x6 &&& 1#64) = 0#64 then 0x1a74 else 0x1a84 := by
  by_cases even : (state.getReg .x6 &&& 1#64) = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend13, pc, even]

theorem execute_advance_right (state : MachineState) (pc : state.pc = 0x1a74)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 43 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 43 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_right_post (state : MachineState) (pc : state.pc = 0x1a74) :
    let after := advancePrefix state 43 2
    after.pc = 0x19cc ∧ after.getReg .x6 = state.getReg .x6 + 1#64 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend21, pc]
  rfl

theorem execute_advance_up (state : MachineState) (pc : state.pc = 0x1a84)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 47 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 47 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_up_post (state : MachineState) (pc : state.pc = 0x1a84) :
    let after := advancePrefix state 47 2
    after.pc = (if state.getReg .x6 >>> 1 = 0#64 then 0x1a8c else 0x1a6c) ∧
      after.getReg .x6 = state.getReg .x6 >>> 1 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  by_cases zero : state.getReg .x6 >>> 1 = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend13, pc, zero] <;> rfl

end TwoPermutationPrototype.PackedOpening
