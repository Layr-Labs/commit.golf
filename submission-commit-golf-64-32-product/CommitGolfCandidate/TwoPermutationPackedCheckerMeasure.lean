import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks
import CommitGolfCandidate.TwoPermutationOpeningGeometry

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype

def measureState (s : MachineState) := execInstrBr s (.MUL .x6 .x16 .x6)

theorem execute_measure (s : MachineState) (pc : s.pc=4100) : Hop s (measureState s) 1 4 := by
  intro fuel
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ (fetch_at s 1 _ (by decide) pc rfl)
    (show ordinaryStep s _=some (measureState s) by rfl)]
  rfl

theorem measure_post (s : MachineState) (pc : s.pc=4100) (factor : s.getReg .x6=500) :
    let next:=measureState s
    next.pc=4104 ∧ next.getReg .x6=s.getReg .x16*500 ∧ next.mem=s.mem ∧
      ∀ r,r≠.x6 → next.getReg r=s.getReg r := by
  refine ⟨?_,?_,rfl,?_⟩
  · change s.pc+4=_;rw [pc];rfl
  · change s.getReg .x16*s.getReg .x6=_;rw [factor]
  · intro r ne
    exact MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)

end TwoPermutationPrototype.Packed.Checker
