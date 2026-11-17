import CommitGolfCandidate.LastLeafOutput

/-! Four fetched instructions close a group of 64 leaves. The last output
register still points to leaf 63, so adding 32 gives the heap position for
the next group. A conditional branch selects a long jump to either target. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def wideLeafBeforeLatch (s : MachineState) (pc : Word) : MachineState :=
  ((s.setReg .x18 (s.getReg .x18 - 1536)).setReg .x23 (s.getReg .x23 - 2048)).setPC pc

def WideLeafFetched (image : Image) (pc : Word) (loopOffset exitOffset : BitVec 21) : Prop :=
  ∀ s : MachineState,
    (s.pc = pc → fetch image s = some (.base (.ADDI .x18 .x18 1536))) ∧
    (s.pc = pc + 4 → fetch image s = some (.base (.ADDI .x23 .x12 32))) ∧
    (s.pc = pc + 8 → fetch image s = some (.base (.BLTU .x23 .x22 8))) ∧
    (s.pc = pc + 12 → fetch image s = some (.base (.JAL .x0 exitOffset))) ∧
    (s.pc = pc + 16 → fetch image s = some (.base (.JAL .x0 loopOffset)))

private theorem wide_leaf_steps (s : MachineState) (pc : Word)
    (lastOutput : s.getReg .x12 + 32 = s.getReg .x23) :
    execInstrBr (execInstrBr (wideLeafBeforeLatch s pc) (.ADDI .x18 .x18 1536))
      (.ADDI .x23 .x12 32) = s.setPC (pc + 8) := by
  cases s with
  | mk regs mem savedPC =>
    change regs .x12 + 32 = regs .x23 at lastOutput
    simp only [wideLeafBeforeLatch, execInstrBr, MachineState.setPC, MachineState.setReg,
        MachineState.getReg, signExtend12, BitVec.add_assoc] <;>
      congr 1 <;> funext r <;> cases r <;>
      first | rfl | exact lastOutput | exact BitVec.sub_add_cancel _ _

private theorem wide_leaf_jump (image : Image) (s : MachineState) (pc target : Word)
    (offset : BitVec 21) (atPC : fetch image (s.setPC pc) = some (.base (.JAL .x0 offset)))
    (jump : pc + signExtend21 offset = target) (fuel : Nat) :
    execute image (1 + fuel) (s.setPC pc) true =
      (do let r ← execute image fuel (s.setPC target) true
          return r.charge 1 0) := by
  have stepped : ordinaryStep (s.setPC pc) (.base (.JAL .x0 offset)) =
      some (s.setPC target) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.setPC,
      MachineState.setReg, jump]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ atPC stepped]
  rfl

theorem wide_leaf_latch (image : Image) (s : MachineState) (pc start exit : Word)
    (loopOffset exitOffset : BitVec 21) (fetched : WideLeafFetched image pc loopOffset exitOffset)
    (loopJump : pc + 16 + signExtend21 loopOffset = start)
    (exitJump : pc + 12 + signExtend21 exitOffset = exit)
    (lastOutput : s.getReg .x12 + 32 = s.getReg .x23) (fuel : Nat) :
    execute image (4 + fuel) (wideLeafBeforeLatch s pc) true =
      (do let result ← execute image fuel (s.setPC
            (if BitVec.ult (s.getReg .x23) (s.getReg .x22) then start else exit)) true
          return result.charge 4 0) := by
  let s0 := wideLeafBeforeLatch s pc
  let s1 := execInstrBr s0 (.ADDI .x18 .x18 1536)
  have step0 : ordinaryStep s0 (.base (.ADDI .x18 .x18 1536)) = some s1 := rfl
  have step1 : ordinaryStep s1 (.base (.ADDI .x23 .x12 32)) = some (s.setPC (pc + 8)) :=
    congrArg some (wide_leaf_steps s pc lastOutput)
  have step2 : ordinaryStep (s.setPC (pc + 8)) (.base (.BLTU .x23 .x22 8)) =
      some (s.setPC (if BitVec.ult (s.getReg .x23) (s.getReg .x22) then pc + 16 else pc + 12)) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, MachineState.getReg,
      MachineState.setPC, signExtend13, BitVec.add_assoc]
    split <;> simp_all
  rw [show 4 + fuel = (1 + fuel) + 1 + 1 + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ ((fetched s0).1 rfl) step0,
    execute_ordinary_step _ _ _ _ _ _ ((fetched s1).2.1 rfl) step1,
    execute_ordinary_step _ _ _ _ _ _ ((fetched _).2.2.1 rfl) step2]
  by_cases repeatGroup : BitVec.ult (s.getReg .x23) (s.getReg .x22) = true
  · simp only [repeatGroup, ite_true]
    rw [wide_leaf_jump image s (pc + 16) start loopOffset ((fetched _).2.2.2.2 rfl) loopJump]
    simp [Execution.charge, instructionCycles, ← Nat.add_assoc]
  · simp only [repeatGroup, Bool.false_eq_true, ite_false]
    rw [wide_leaf_jump image s (pc + 12) exit exitOffset ((fetched _).2.2.2.1 rfl) exitJump]
    simp [Execution.charge, instructionCycles, ← Nat.add_assoc]

end CommitGolfCandidate
