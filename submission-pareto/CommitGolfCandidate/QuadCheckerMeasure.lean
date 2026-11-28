import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

/-! Word 1 of the checker, `mul t1, a6, t1`: the record count times the record width. The donor's
word 0 (`addi t1, x0, 2200`) now jumps to the cap wrapper, which sets `t1 = 2200` itself and
returns here. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

def measureState (state : MachineState) := execInstrBr state (.MUL .x6 .x16 .x6)

theorem execute_measure (state : MachineState) (pc : state.pc = 4100) :
    Hop state (measureState state) 1 4 := by
  intro fuel
  have first := fetch_at state 1 (.MUL .x6 .x16 .x6) (by decide) pc rfl
  have execFirst : ordinaryStep state (.base (.MUL .x6 .x16 .x6)) = some (measureState state) := rfl
  rw [show 1+fuel = fuel+1 by omega, execute_ordinary_step _ _ _ _ _ _ first execFirst]
  simp [instructionCycles, Execution.charge, bind_assoc, ← Nat.add_assoc]

theorem measure_post (state : MachineState) (pc : state.pc = 4100) :
    let next := measureState state
    next.pc = 4104 ∧ next.getReg .x6 = state.getReg .x16*state.getReg .x6 ∧
      next.mem = state.mem ∧ ∀ r, r ≠ .x6 → next.getReg r = state.getReg r := by
  refine ⟨?_,?_,rfl,?_⟩
  · change state.pc+4 = _
    rw [pc]
    rfl
  · simp [measureState,execInstrBr,MachineState.getReg_setPC,Opening.getReg_setReg]
  · intro r saved
    simp [measureState,execInstrBr,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm saved)]

end TwoPermutationPrototype.Quad.Checker
