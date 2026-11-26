import CommitGolfCandidate.ChainedPrefixInvariant
import CommitGolfCandidate.TwoPermutationPackedOpeningImage

/-! Conservative direct control-flow targets for ordinary RV64 instructions. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def directTargets (pc : Word) : Instruction → Option (List Word)
  | .base (.JAL _ offset) => some [pc+signExtend21 offset]
  | .base (.JALR ..) => none
  | .base (.BEQ _ _ offset) | .base (.BNE _ _ offset) | .base (.BLT _ _ offset)
  | .base (.BGE _ _ offset) | .base (.BLTU _ _ offset) | .base (.BGEU _ _ offset) =>
      some [pc+signExtend13 offset,pc+4]
  | _ => some [pc+4]

theorem ordinary_step_target (s next : MachineState) (instruction : Instruction) (targets : List Word)
    (known : directTargets s.pc instruction=some targets) (step : ordinaryStep s instruction=some next) :
    next.pc∈targets := by
  cases instruction with
  | word op rd rs1 rs2 =>
    simp only [ordinaryStep,Option.some.injEq] at step
    subst next
    cases known
    simp [MachineState.setPC]
  | sraiw rd rs shift =>
    simp only [ordinaryStep,Option.some.injEq] at step
    subst next
    cases known
    simp [MachineState.setPC]
  | base instruction =>
    cases instruction <;>
      simp only [ordinaryStep,reduceCtorEq,Option.ite_none_right_eq_some,Option.some.injEq] at step <;>
      simp only [directTargets,Option.some.injEq,reduceCtorEq] at known <;>
      obtain ⟨_,rfl⟩ := step <;> subst targets <;>
      simp only [execInstrBr,MachineState.setPC] <;>
      (try split) <;> simp

end CommitGolfCandidate.Chained.Native
