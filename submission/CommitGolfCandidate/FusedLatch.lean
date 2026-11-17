import CommitGolfCandidate.FusedTail

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fusedLatchInstructions : List Instr :=
  [.ADDI .x18 .x18 24, .ADDI .x23 .x23 32, .BLTU .x23 .x22 7912]

def fusedLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (fusedLatchInstructions.take count).foldl execInstrBr state

def FusedLatchFetched (image : Image) : Prop :=
  ∀ state : MachineState, ∀ i < 3, state.pc = 4552 →
    fetch image (fusedLatchPrefix state i) =
      some (.base ((fusedLatchInstructions[i]?).getD .EBREAK))

def fusedLatchState (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 + 24)).setReg .x23
    (state.getReg .x23 + 32)).setPC
      (if BitVec.ult (state.getReg .x23 + 32) (state.getReg .x22)
        then 4280 else 4564)

theorem fused_latch_state (state : MachineState) (pc : state.pc = 4552) :
    fusedLatchPrefix state 3 = fusedLatchState state := by
  simp [fusedLatchPrefix, fusedLatchInstructions, List.foldl, execInstrBr,
    signExtend12, signExtend13, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, fusedLatchState, pc]
  split <;> simp_all

theorem fused_latch_execute (image : Image) (fetched : FusedLatchFetched image)
    (state : MachineState) (pc : state.pc = 4552) (fuel : Nat) :
    execute image (3 + fuel) state true =
      (do let result ← execute image fuel (fusedLatchState state) true
          return result.charge 3 0) := by
  have trace : execute image (3 + fuel) state true =
      (do let result ← execute image fuel (fusedLatchPrefix state 3) true
          return result.charge 3 0) := by
    apply execute_unit_steps (states := fusedLatchPrefix state)
    intro i hi
    refine ⟨.base ((fusedLatchInstructions[i]?).getD .EBREAK),
      fetched state i hi pc, ?_, ?_⟩
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  rw [fused_latch_state state pc] at trace
  exact trace

theorem fused_latch_frame (state : MachineState) (messageBase : Word) :
    fusedLatchState (cursorNormalize state messageBase 4552) =
      cursorNormalize (commitPositionNextState state) messageBase
        (if BitVec.ult (state.getReg .x23 + 32) (state.getReg .x22)
          then 4280 else 4564) := by
  cases state
  dsimp [fusedLatchState, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    commitPositionNextState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

end CommitGolfCandidate
