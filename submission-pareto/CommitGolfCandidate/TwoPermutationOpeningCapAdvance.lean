import CommitGolfCandidate.TwoPermutationOpeningCapCursor

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem step_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem step_zeroreg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

def advancePrefix (state : MachineState) (index count : Nat) : MachineState :=
  ((capWalkInstructions.drop index).take count).foldl execInstrBr state

/-- Two adjacent, ordinary cap instructions with no accessed memory. The first
instruction in each such pair follows the straight-line PC. -/
private theorem execute_cap_pair (state : MachineState) (index : Nat) (fuel : Nat)
    (allowCoins : Bool) (bounded : index + 1 < 27)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (248 + index)))
    (firstPC : (advancePrefix state index 1).pc = BitVec.ofNat 64 (4096 + 4 * (248 + (index + 1))))
    (trace : ∀ i < 2,
      (openingImage.code[248 + (index + i)]?).bind decodeInstruction =
        some (.base ((capWalkInstructions.drop index)[i]?.getD .EBREAK)) ∧
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
  apply opening_fetch _ (248 + (index + i)) _ (by omega) _ decodes
  interval_cases i
  · exact pc
  · exact firstPC

/-- The parity test falls through for an even node and jumps for an odd node. -/
theorem execute_advance_parity_test (state : MachineState) (pc : state.pc = 0x142c)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 19 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 19 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_parity_target (state : MachineState) (pc : state.pc = 0x142c) :
    (advancePrefix state 19 2).pc =
      if (state.getReg .x6 &&& 1#64) = 0#64 then 0x1434 else 0x1444 := by
  by_cases even : (state.getReg .x6 &&& 1#64) = 0#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend13, pc, even]

theorem execute_advance_right (state : MachineState) (pc : state.pc = 0x1434)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 21 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 21 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_right_post (state : MachineState) (pc : state.pc = 0x1434) :
    let after := advancePrefix state 21 2
    after.pc = 0x13e4 ∧ after.getReg .x6 = state.getReg .x6 + 1#64 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, signExtend21, pc]
  rfl

theorem execute_advance_up (state : MachineState) (pc : state.pc = 0x1444)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 25 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 25 _ _ (by decide) pc
  · simp [advancePrefix, capWalkInstructions, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_up_post (state : MachineState) (pc : state.pc = 0x1444) :
    let after := advancePrefix state 25 2
    after.pc = (if state.getReg .x6 >>> 1 = 0#64 then 0x144c else 0x142c) ∧
      after.getReg .x6 = state.getReg .x6 >>> 1 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  by_cases zero : state.getReg .x6 >>> 1 = 0#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend13, pc, zero] <;> rfl

end TwoPermutationPrototype.Opening
