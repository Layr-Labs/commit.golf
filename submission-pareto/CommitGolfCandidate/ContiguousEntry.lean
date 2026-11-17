import CommitGolfCandidate.ContiguousLoop

/-! Two real entry jumps establish the fixed return link once. Positive-head
reference erasure later removes this preparation from the scheme distribution. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ContiguousEntryFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4280 → fetch image state = some (.base (.JAL .x0 32))) ∧
    (state.pc = 4312 → fetch image state = some (.base (.JAL .x1 144)))

theorem contiguous_entry (image : Image) (fetched : ContiguousEntryFetched image)
    (state : MachineState) (pc : state.pc = 4280) (fuel : Nat) :
    execute image (2 + fuel) state true =
      (do let result ← execute image fuel ((state.setReg .x1 4316).setPC 4456) true
          return result.charge 2 0) := by
  have first : ordinaryStep state (.base (.JAL .x0 32)) =
      some (state.setPC 4312) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      pc, MachineState.setReg]
  have second : ordinaryStep (state.setPC 4312) (.base (.JAL .x1 144)) =
      some ((state.setReg .x1 4316).setPC 4456) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setPC, MachineState.setReg]
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ ((fetched state).1 pc) first]
  rw [execute_ordinary_step _ _ _ _ _ _ ((fetched (state.setPC 4312)).2 rfl) second]
  simp [pure_bind, Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem contiguous_link_invariant (state : MachineState) (remaining : Nat) (value : Word)
    (invariant : CommitLeavesInvariant state remaining) :
    CommitLeavesInvariant (state.setReg .x1 value) remaining := by
  rcases invariant with ⟨pc, counter, bounded, scratch, above, message, salts, heap,
    ready, block⟩
  refine ⟨pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using counter
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using bounded
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using scratch
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using above
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using message
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using salts
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using heap
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using ready
  · simpa [CommitLeafOracleReady, StreamingOracleReady, MachineState.setReg, MachineState.getReg] using block

theorem contiguous_entry_frame (state : MachineState) (messageBase : Word) :
    ((cursorLeafFrame state messageBase).setReg .x1 4316).setPC 4456 =
      cursorNormalize (state.setReg .x1 4316) messageBase 4456 := by
  cases state
  dsimp [cursorNormalize, cursorLeafFrame, cursorBaseFrame, MachineState.setReg,
    MachineState.getReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

end CommitGolfCandidate
