import CommitGolfCandidate.NonceStateEquiv
import CommitGolfCandidate.NonceCheckControlTable

/-! Actual ordinary checker instructions respect aligned-word observational
equality, including admitted aligned loads and stores. Faults coincide. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

inductive NonceStepEquiv : Option MachineState → Option MachineState → Prop where
  | fault : NonceStepEquiv none none
  | next {left right : MachineState} (related : NonceStateEquiv left right) :
      NonceStepEquiv (some left) (some right)

namespace NonceStateEquiv

private theorem memory_arguments (left right : MachineState) (related : NonceStateEquiv left right)
    (instruction : Instr) : memoryArgumentsValid left instruction=memoryArgumentsValid right instruction := by
  cases instruction <;> simp only [memoryArgumentsValid,memAccess,related.registers]

private theorem matching_step (leftValid rightValid : Bool) (leftNext rightNext : MachineState)
    (same : leftValid=rightValid) (effects : leftValid=true → NonceStateEquiv leftNext rightNext) :
    NonceStepEquiv (if leftValid then some leftNext else none) (if rightValid then some rightNext else none) := by
  rw [←same]
  by_cases valid : leftValid=true
  · simp only [if_pos valid]
    exact .next (effects valid)
  · simp only [if_neg valid]
    exact .fault

private theorem ld_value (left right : MachineState) (related : NonceStateEquiv left right)
    (rd source : Reg) (offset : BitVec 12)
    (valid : memoryArgumentsValid left (.LD rd source offset)=true) :
    left.getMem (right.getReg source+signExtend12 offset)=
      right.getMem (right.getReg source+signExtend12 offset) := by
  apply related.memory
  simp only [memoryArgumentsValid,memAccess,related.registers] at valid
  simp only [accessValid,Bool.and_eq_true,decide_eq_true_eq] at valid
  exact valid.2

theorem checked_ordinary (left right : MachineState) (related : NonceStateEquiv left right)
    (instruction : Instr) (safe : NonceCheckControl.checked left.pc (.base instruction)=true) :
    NonceStepEquiv (ordinaryStep left (.base instruction)) (ordinaryStep right (.base instruction)) := by
  cases instruction <;> simp only [NonceCheckControl.checked,Bool.false_eq_true] at safe
  all_goals first
    | exact .fault
    | apply matching_step _ _ _ _ (memory_arguments left right related _)
  all_goals intro valid
  all_goals simp only [execInstrBr,related.registers,related.pc]
  all_goals first
    | apply set_pc
      exact set_reg left right related _ _
    | apply set_pc
      exact set_mem left right related _ _
    | rw [ld_value left right related _ _ _ valid]
      apply set_pc
      exact set_reg left right related _ _
    | split <;> exact set_pc left right related _

theorem ordinary (left right : MachineState) (related : NonceStateEquiv left right)
    (instruction : Instruction) (safe : NonceCheckControl.checked left.pc instruction=true) :
    NonceStepEquiv (ordinaryStep left instruction) (ordinaryStep right instruction) := by
  cases instruction with
  | base instruction => exact checked_ordinary left right related instruction safe
  | word op rd first second => simp only [NonceCheckControl.checked,Bool.false_eq_true] at safe
  | sraiw rd source shift => simp only [NonceCheckControl.checked,Bool.false_eq_true] at safe

end NonceStateEquiv
end CommitGolfCandidate
