import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

def measureState (s : MachineState) := execInstrBr s (.MUL .x6 .x16 .x6)

theorem execute_measure (s : MachineState) (here : s.pc=4100) : Hop s (measureState s) 1 4 := by
  intro fuel
  have fetched:=fetch_at s 1 (.MUL .x6 .x16 .x6) (by decide) here rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched (show ordinaryStep s _=some (measureState s) from rfl)]
  rfl

theorem measure_post (state : MachineState) (pc : state.pc = 4100) (factor : state.getReg .x6=534) :
    let next := measureState state
    next.pc = 4104 ∧ next.getReg .x6 = state.getReg .x16*534 ∧
      next.mem = state.mem ∧ ∀ r, r ≠ .x6 → next.getReg r = state.getReg r := by
  have zero : state.getReg .x0 = 0#64 := rfl
  refine ⟨?_,?_,rfl,?_⟩
  · change state.pc+4 = _
    rw [pc]
    rfl
  · simp [measureState,factor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      Opening.getReg_setReg]
  · intro r saved
    simp [measureState,factor,execInstrBr,signExtend12,zero,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm saved)]

end TwoPermutationPrototype.Packed.Checker
