import CommitGolfCandidate.GroupOpenCapCursor

namespace TwoPermutationPrototype.GroupedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem step_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem step_zeroreg (state : MachineState) : state.getReg .x0 = 0#64 := rfl

/-- Rows 701..708. 701/702: parity test; an even node branches to row 660 (`addi x6,x6,1`), which falls
into the lookup at 661. 703/704: an odd node climbs to its parent and loops back to 701 while the parent
is not the root (`x23 = 1`); 705: the root exit `jal` to the return block at 709. Rows 706..708 are no
longer reached. -/
def advanceCode : List Instr :=
  [.ANDI .x7 .x6 1, .BEQ .x7 .x0 8024, .SRLI .x6 .x6 1, .BNE .x6 .x23 8180,
   .JAL .x0 16, .ADDI .x0 .x0 0, .ADDI .x6 .x6 1, .JAL .x0 2096964]

theorem at_parity_test : capWalkInstructions.drop 41 = advanceCode := rfl
theorem at_parent_step : capWalkInstructions.drop 43 = advanceCode.drop 2 := rfl

attribute [local simp] at_parity_test at_parent_step

def advancePrefix (state : MachineState) (index count : Nat) : MachineState :=
  ((capWalkInstructions.drop index).take count).foldl execInstrBr state

/-- Two adjacent, ordinary cap instructions with no accessed memory. The first
instruction in each such pair follows the straight-line PC. -/
private theorem execute_cap_pair (state : MachineState) (index : Nat) (fuel : Nat)
    (allowCoins : Bool) (bounded : index + 1 < 49)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (660 + index)))
    (firstPC : (advancePrefix state index 1).pc = BitVec.ofNat 64 (4096 + 4 * (660 + (index + 1))))
    (trace : ∀ i < 2,
      (openingImage.code[660 + (index + i)]?).bind Opening.decodeBase =
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
  apply packed_fetch_base _ (660 + (index + i)) _ (by omega) _ decodes
  interval_cases i
  · exact pc
  · exact firstPC

/-- Rows 701, 702: `andi x7,x6,1; beq x7,x0,<660>`. -/
theorem execute_advance_parity_test (state : MachineState) (pc : state.pc = 0x1af4)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 41 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 41 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_parity_target (state : MachineState) (pc : state.pc = 0x1af4) :
    (advancePrefix state 41 2).pc =
      if (state.getReg .x6 &&& 1#64) = 0#64 then 0x1a50 else 0x1afc := by
  by_cases even : (state.getReg .x6 &&& 1#64) = 0#64 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend12, signExtend13, pc, even]

/-- Row 660: `addi x6,x6,1`, falling into the lookup at 661. -/
def advanceRightStep (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x6 .x6 1)

theorem execute_advance_right (state : MachineState) (pc : state.pc = 0x1a50)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advanceRightStep state) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 660 (.ADDI .x6 .x6 1) (by decide) pc (by decide +kernel)
  have step : ordinaryStep state (.base (.ADDI .x6 .x6 1)) = some (advanceRightStep state) := rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem advance_right_post (state : MachineState) (pc : state.pc = 0x1a50) :
    let after := advanceRightStep state
    after.pc = 0x1a54 ∧ after.getReg .x6 = state.getReg .x6 + 1#64 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  simp [advanceRightStep, execInstrBr, signExtend12, pc] <;> rfl

/-- Rows 703, 704: `srli x6,x6,1; bne x6,x23,<701>`. -/
theorem execute_advance_up (state : MachineState) (pc : state.pc = 0x1afc)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (2 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (advancePrefix state 43 2) allowCoins
          return result.charge 2 0) := by
  apply execute_cap_pair _ 43 _ _ (by decide) pc
  · simp [advancePrefix, advanceCode, execInstrBr, pc]
  · intro i hi
    interval_cases i <;> exact ⟨rfl, rfl, rfl⟩

theorem advance_up_post (state : MachineState) (pc : state.pc = 0x1afc) :
    let after := advancePrefix state 43 2
    after.pc = (if state.getReg .x6 >>> 1 = state.getReg .x23 then 0x1b04 else 0x1af4) ∧
      after.getReg .x6 = state.getReg .x6 >>> 1 ∧
      after.getReg .x21 = state.getReg .x21 ∧ after.mem = state.mem := by
  by_cases taken : state.getReg .x6 >>> 1 = state.getReg .x23 <;>
    simp [advancePrefix, advanceCode, execInstrBr, signExtend13, pc, taken] <;> rfl

/-- Row 705: the root exit `jal x0,<709>`. -/
theorem execute_advance_exit (state : MachineState) (pc : state.pc = 0x1b04)
    (fuel : Nat) (allowCoins : Bool) :
    execute openingImage (1 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (state.setPC 0x1b14) allowCoins
          return result.charge 1 0) := by
  have fetched := packed_fetch_base state 705 (.JAL .x0 16) (by decide) pc (by decide +kernel)
  have step : ordinaryStep state (.base (.JAL .x0 16)) = some (state.setPC 0x1b14) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

end TwoPermutationPrototype.GroupedOpening
