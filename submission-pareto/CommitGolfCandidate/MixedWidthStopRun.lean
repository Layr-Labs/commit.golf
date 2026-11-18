import CommitGolfCandidate.MixedWidthParentImage
import CommitGolfCandidate.MixedWidthStopSetup

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute

private def mixedStopPrefix (state : MachineState) (i : Nat) : MachineState :=
  (mixedStopOps.take i).foldl execInstrBr state

private theorem mixed_stop_fetch (i : Fin 3) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (184628+4*i.val)) :
    fetch packedWideCommitImage state=some (.base ((mixedStopOps[i.val]?).getD .EBREAK)) := by
  have address : state.pc=BitVec.ofNat 64 (4096+4*(45133+i.val)) := by
    rw [pc]
    congr 1
    omega
  have fetched := packed_index_fetch state (45133+i.val) address (by omega) (by have := i.isLt; omega)
  fin_cases i <;> exact fetched

theorem execute_mixed_stop (state : MachineState) (pc : state.pc=184628) (fuel : Nat) :
    execute packedWideCommitImage (3+fuel) state true =
      (do let result ← execute packedWideCommitImage fuel (mixedStopSetup state) true
          return result.charge 3 0) := by
  have finalState : mixedStopPrefix state 3=mixedStopSetup state := rfl
  rw [←finalState]
  apply CommitGolfCandidate.execute_unit_steps (states := mixedStopPrefix state)
  intro i inside
  refine ⟨.base ((mixedStopOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have atPC : (mixedStopPrefix state i).pc=BitVec.ofNat 64 (184628+4*i) := by
      interval_cases i <;>
        simp only [mixedStopPrefix,mixedStopOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have fetched := mixed_stop_fetch ⟨i,inside⟩ (mixedStopPrefix state i) atPC
    interval_cases i <;> exact fetched
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

end TwoPermutationPrototype.RV64
