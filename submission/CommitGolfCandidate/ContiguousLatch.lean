import CommitGolfCandidate.ContiguousTail
import CommitGolfCandidate.ContiguousReference

/-! The heap-end latch follows the final leaf query without a return. It
advances the live salt and heap pointers and either repeats the salt-copy entry
or falls through to a separately charged exit jump. Fetch premises are explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def contiguousLatchInstructions : List Instr :=
  [.ADDI .x18 .x18 24, .ADDI .x23 .x23 32, .BLTU .x23 .x22 8060]

def contiguousLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (contiguousLatchInstructions.take count).foldl execInstrBr state

def ContiguousLatchFetched (image : Image) : Prop :=
  ∀ state : MachineState, ∀ i < 3, state.pc = 4580 →
    fetch image (contiguousLatchPrefix state i) =
      some (.base ((contiguousLatchInstructions[i]?).getD .EBREAK))

def contiguousLatchState (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 + 24)).setReg .x23
    (state.getReg .x23 + 32)).setPC
      (if BitVec.ult (state.getReg .x23 + 32) (state.getReg .x22)
        then 4456 else 4592)

theorem contiguous_latch_state (state : MachineState) (pc : state.pc = 4580) :
    contiguousLatchPrefix state 3 = contiguousLatchState state := by
  simp [contiguousLatchPrefix, contiguousLatchInstructions, List.foldl, execInstrBr,
    signExtend12, signExtend13, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, contiguousLatchState, pc]
  split <;> simp_all

/-- Three real ordinary instructions cost three cycles, with no leaf return. -/
theorem contiguous_latch_execute (image : Image) (fetched : ContiguousLatchFetched image)
    (state : MachineState) (pc : state.pc = 4580) (fuel : Nat) :
    execute image (3 + fuel) state true =
      (do let result ← execute image fuel (contiguousLatchState state) true
          return result.charge 3 0) := by
  have trace : execute image (3 + fuel) state true =
      (do let result ← execute image fuel (contiguousLatchPrefix state 3) true
          return result.charge 3 0) := by
    apply execute_unit_steps (states := contiguousLatchPrefix state)
    intro i hi
    refine ⟨.base ((contiguousLatchInstructions[i]?).getD .EBREAK),
      fetched state i hi pc, ?_, ?_⟩
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  rw [contiguous_latch_state state pc] at trace
  exact trace

theorem contiguous_latch_frame (state : MachineState) (messageBase : Word) :
    contiguousLatchState (cursorNormalize state messageBase 4580) =
      cursorNormalize (commitPositionNextState state) messageBase
        (if BitVec.ult (state.getReg .x23 + 32) (state.getReg .x22)
          then 4456 else 4592) := by
  cases state
  dsimp [contiguousLatchState, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    commitPositionNextState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

end CommitGolfCandidate
