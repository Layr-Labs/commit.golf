import CommitGolfCandidate.TwoPermutationPackedCapFetch

/-! # The frontier read dispatch (T238)

From word 294: `slli x7,x6,5; add x7,x25,x7; jal <631>` then `bne x30,x0,<692>` (the countdown `x30` is zero on the
last node of a group of eight). Normal node: `addi x30,x30,-1; addi x28,x21,30; jal <297>; bltu x22,x28,<364>`.
Last node of a group: `addi x28,x21,28; bltu x22,x28,<364>` (632..633). -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64

set_option maxRecDepth 4096
attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg
@[local simp] private theorem pc_after (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
@[local simp] private theorem zero_register (state : MachineState) : state.getReg .x0 = 0#64 := rfl
@[local simp] private theorem set_zero (state : MachineState) (v : Word) : state.setReg .x0 v = state := rfl
@[local simp] private theorem minus_one (x : Word) : x + 18446744073709551615#64 = x - 1#64 := by
  rw [BitVec.sub_eq_add_neg]
  rfl

def frontierHeadCode : List Instr := [.SLLI .x7 .x6 5, .ADD .x7 .x25 .x7, .JAL .x0 1340, .BNE .x30 .x0 244]
def frontierHeadWords : List Nat := [294, 295, 296, 631]

def frontierHead (state : MachineState) : MachineState := (frontierHeadCode.take 4).foldl execInstrBr state

private def headPrefix (state : MachineState) (count : Nat) : MachineState :=
  (frontierHeadCode.take count).foldl execInstrBr state

theorem execute_frontier_head (state : MachineState) (pc : state.pc = 0x1498) (fuel : Nat) :
    execute packedImage (4+fuel) state false =
      (do let next ← execute packedImage fuel (frontierHead state) false
          return next.charge 4 0) := by
  apply execute_unit_steps (states := headPrefix state)
  intro i bounded
  refine ⟨.base (frontierHeadCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (frontierHeadWords.getD i 0) _ (by interval_cases i <;> decide)
    · interval_cases i <;> simp [headPrefix, frontierHeadCode, frontierHeadWords, execInstrBr, signExtend21, pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem frontier_head_post (state : MachineState) (pc : state.pc = 0x1498) :
    let next := frontierHead state
    next.pc = (if state.getReg .x30 = 0#64 then 0x19e0 else 0x1ad0) ∧
    next.getReg .x7 = state.getReg .x25+(state.getReg .x6 <<< 5) ∧ next.mem = state.mem := by
  by_cases last : state.getReg .x30 = 0#64
  · refine ⟨?_, ?_, ?_⟩ <;> simp [frontierHead, frontierHeadCode, execInstrBr, signExtend13, signExtend21, pc, last]
      <;> rfl
  · refine ⟨?_, ?_, ?_⟩ <;> simp [frontierHead, frontierHeadCode, execInstrBr, signExtend13, signExtend21, pc, last]
      <;> rfl

theorem frontier_head_register (state : MachineState) (r : Reg) (dest : r ≠ .x7) :
    (frontierHead state).getReg r = state.getReg r := by
  by_cases last : state.getReg .x30 = 0#64
  · simp [frontierHead, frontierHeadCode, execInstrBr, Ne.symm dest, last]
  · simp [frontierHead, frontierHeadCode, execInstrBr, Ne.symm dest, last]

/-! ### Normal node: count down, bound the 30-byte read -/

def normalGuardCode : List Instr := [.ADDI .x30 .x30 4095, .ADDI .x28 .x21 30, .JAL .x0 2095564, .BLTU .x22 .x28 268]
def normalGuardWords : List Nat := [692, 693, 694, 297]

def normalGuard (state : MachineState) : MachineState := (normalGuardCode.take 4).foldl execInstrBr state

private def normalPrefix (state : MachineState) (count : Nat) : MachineState :=
  (normalGuardCode.take count).foldl execInstrBr state

theorem execute_normal_guard (state : MachineState) (pc : state.pc = 0x1ad0) (fuel : Nat) :
    execute packedImage (4+fuel) state false =
      (do let next ← execute packedImage fuel (normalGuard state) false
          return next.charge 4 0) := by
  apply execute_unit_steps (states := normalPrefix state)
  intro i bounded
  refine ⟨.base (normalGuardCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (normalGuardWords.getD i 0) _ (by interval_cases i <;> decide)
    · interval_cases i <;> simp [normalPrefix, normalGuardCode, normalGuardWords, execInstrBr, signExtend21, pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem normal_guard_post (state : MachineState) (pc : state.pc = 0x1ad0) :
    let next := normalGuard state
    next.pc = (if state.getReg .x22 < state.getReg .x21+30#64 then 0x15b0 else 0x14a8) ∧
    next.getReg .x30 = state.getReg .x30 - 1#64 ∧
    next.getReg .x28 = state.getReg .x21+30#64 ∧ next.mem = state.mem := by
  by_cases short : state.getReg .x22 < state.getReg .x21+30#64
  · have branch : (state.getReg .x22).ult (state.getReg .x21+30#64) = true := decide_eq_true short
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [normalGuard, normalGuardCode, execInstrBr, signExtend12, signExtend13, signExtend21, pc, short, branch]
      <;> rfl
  · have branch : (state.getReg .x22).ult (state.getReg .x21+30#64) = false := decide_eq_false short
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [normalGuard, normalGuardCode, execInstrBr, signExtend12, signExtend13, signExtend21, pc, short, branch]
      <;> rfl

theorem normal_guard_register (state : MachineState) (r : Reg) (count : r ≠ .x30) (bound : r ≠ .x28) :
    (normalGuard state).getReg r = state.getReg r := by
  by_cases short : (state.getReg .x22).ult (state.getReg .x21+30#64)
  · simp [normalGuard, normalGuardCode, execInstrBr, signExtend12, Ne.symm count, Ne.symm bound, short]
  · simp [normalGuard, normalGuardCode, execInstrBr, signExtend12, Ne.symm count, Ne.symm bound, short]

/-! ### Last node of a group: bound the 28-byte read -/

def eighthGuardCode : List Instr := [.ADDI .x28 .x21 28, .BLTU .x22 .x28 7116]
def eighthGuardWords : List Nat := [632, 633]

def eighthGuard (state : MachineState) : MachineState := (eighthGuardCode.take 2).foldl execInstrBr state

private def eighthPrefix (state : MachineState) (count : Nat) : MachineState :=
  (eighthGuardCode.take count).foldl execInstrBr state

theorem execute_eighth_guard (state : MachineState) (pc : state.pc = 0x19e0) (fuel : Nat) :
    execute packedImage (2+fuel) state false =
      (do let next ← execute packedImage fuel (eighthGuard state) false
          return next.charge 2 0) := by
  apply execute_unit_steps (states := eighthPrefix state)
  intro i bounded
  refine ⟨.base (eighthGuardCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_fetch _ (eighthGuardWords.getD i 0) _ (by interval_cases i <;> decide)
    · interval_cases i <;> simp [eighthPrefix, eighthGuardCode, eighthGuardWords, execInstrBr, pc] <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem eighth_guard_post (state : MachineState) (pc : state.pc = 0x19e0) :
    let next := eighthGuard state
    next.pc = (if state.getReg .x22 < state.getReg .x21+28#64 then 0x15b0 else 0x19e8) ∧
    next.getReg .x28 = state.getReg .x21+28#64 ∧ next.mem = state.mem := by
  by_cases short : state.getReg .x22 < state.getReg .x21+28#64
  · have branch : (state.getReg .x22).ult (state.getReg .x21+28#64) = true := decide_eq_true short
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [eighthGuard, eighthGuardCode, execInstrBr, signExtend12, signExtend13, pc, short, branch] <;> rfl
  · have branch : (state.getReg .x22).ult (state.getReg .x21+28#64) = false := decide_eq_false short
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [eighthGuard, eighthGuardCode, execInstrBr, signExtend12, signExtend13, pc, short, branch] <;> rfl

theorem eighth_guard_register (state : MachineState) (r : Reg) (bound : r ≠ .x28) :
    (eighthGuard state).getReg r = state.getReg r := by
  by_cases short : (state.getReg .x22).ult (state.getReg .x21+28#64)
  · simp [eighthGuard, eighthGuardCode, execInstrBr, signExtend12, Ne.symm bound, short]
  · simp [eighthGuard, eighthGuardCode, execInstrBr, signExtend12, Ne.symm bound, short]

/-! ### The node's final pointer step at 329 (normal node) -/

def frontierFinish (state : MachineState) :=
  (state.setReg .x21 (state.getReg .x21+30#64)).setPC 0x1528

theorem execute_frontier_finish (state : MachineState) (pc : state.pc = 0x1524) (fuel : Nat) :
    execute packedImage (1+fuel) state false =
      (do let result ← execute packedImage fuel (frontierFinish state) false
          return result.charge 1 0) := by
  have fetched := cap_fetch state 329 (.ADDI .x21 .x21 30) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.ADDI .x21 .x21 30)) = some (frontierFinish state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, frontierFinish, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

end TwoPermutationPrototype.Packed.Checker
