import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

private def setFactor (state : MachineState) := execInstrBr state (.ADDI .x6 .x0 498)
def measureState (state : MachineState) := execInstrBr (setFactor state) (.MUL .x6 .x16 .x6)

theorem measure_post (state : MachineState) (pc : state.pc = 4096) :
    let next := measureState state
    next.pc = 4104 ∧ next.getReg .x6 = state.getReg .x16*498 ∧
      next.mem = state.mem ∧ ∀ r, r ≠ .x6 → next.getReg r = state.getReg r := by
  have zero : state.getReg .x0 = 0#64 := rfl
  refine ⟨?_,?_,rfl,?_⟩
  · change state.pc+4+4 = _
    rw [pc]
    rfl
  · simp [measureState,setFactor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      Opening.getReg_setReg]
  · intro r saved
    simp [measureState,setFactor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm saved)]

end TwoPermutationPrototype.Packed.Checker
