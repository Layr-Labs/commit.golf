import CommitGolfCandidate.GroupedScan
import CommitGolfCandidate.TwoPermutationParentEntry

/-! The five parent-setup words of 04680e02, moved by one artifact chunk to words 45,672-45,676 in the P4 image
(04680e02 `TwoPermutationPackedSetup.packed_execute_wide_parent_setup`/`packed_wide_parent_setup_ready`, with the
fetch taken from the grouped image). -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

private theorem parent_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (codeWord (45672+i.val))=some ((parentSetupOps[i.val]?).getD .EBREAK) := by
  decide +kernel

theorem fetch_parent_setup (i : Fin 5) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(45672+i.val))) :
    fetch image state=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  have fits : 45672+i.val<233357 := by have := i.isLt; omega
  exact fetch_decoded state _ fits pc _ (parent_setup_decoded i)

theorem execute_parent_setup (state : MachineState) (atSetup : state.pc=186784) (fuel : Nat) :
    execute image (5+fuel) state true =
      (do let out ← execute image fuel (parentSetup state 5) true
          return out.charge 5 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup state)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have pc : (parentSetup state i).pc=BitVec.ofNat 64 (4096+4*(45672+i)) := by
      interval_cases i <;>
        simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,atSetup] <;> rfl
    exact fetch_parent_setup ⟨i,inside⟩ (parentSetup state i) pc
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem parent_setup_ready (state : MachineState) (atSetup : state.pc=186784)
    (selector : state.getReg .x5=0) (heap : state.getReg .x9=4294971424)
    (stride : state.getReg .x19=536870912)
    (stop : state.getReg .x21=wordAddress (leafDest (2^24))) :
    ParentRegs (parentSetup state 5) (2^24-1) ∧ (parentSetup state 5).pc=186804 ∧
      (parentSetup state 5).getReg .x8=state.getReg .x8 := by
  refine ⟨⟨?_,?_,selector,rfl,rfl,heap⟩,?_,rfl⟩
  · change state.getReg .x21+signExtend12 4032=_
    rw [stop]
    rfl
  · change state.getReg .x21-state.getReg .x19+signExtend12 4064=_
    rw [stop,stride]
    rfl
  · change state.pc+4+4+4+4+4=_
    rw [atSetup]
    rfl

end TwoPermutationPrototype.Grouped
