import CommitGolfCandidate.Compact.NoJumpImage
/-! Checked entry sequence and empty-opening branch for the unrolled image.
The register setup agrees with the existing reference execution. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def noJumpSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0,.ADDI .x24 .x13 0,.ADDI .x25 .x15 0,.ADDI .x27 .x16 0,
   .LUI .x19 4096,.LUI .x6 262144,.ADD .x18 .x9 .x6,.JAL .x0 48,
   .BEQ .x27 .x0 1320]
def noJumpSetupPrefix (s : MachineState) (count : Nat) : MachineState :=
  (noJumpSetupInstructions.take count).foldl execInstrBr s

def noJumpInitializedState (s : MachineState) : MachineState :=
  (openingInitializedState s).setPC (if s.getReg .x16=0 then 5492 else 4176)

theorem noJump_setup_same (s : MachineState) (pc : s.pc=4096) :
    noJumpSetupPrefix s 9=noJumpInitializedState s := by
  have expansion (s : MachineState) : openingInitializedState s=
      (([.ADDI .x9 .x12 0,.ADDI .x24 .x13 0,.ADDI .x25 .x15 0,.ADDI .x27 .x16 0,
        .ADDI .x19 .x0 0,.SLLI .x19 .x19 11,.ADDI .x19 .x19 4,
        .SLLI .x19 .x19 11,.ADDI .x19 .x19 0,.SLLI .x19 .x19 11,.ADDI .x19 .x19 0,
        .ADDI .x6 .x0 0,.SLLI .x6 .x6 11,.ADDI .x6 .x6 256,
        .SLLI .x6 .x6 11,.ADDI .x6 .x6 0,.SLLI .x6 .x6 11,.ADDI .x6 .x6 0,
        .ADD .x18 .x9 .x6] : List Instr).foldl execInstrBr s).setPC
        (if s.getReg .x16=0 then 4320 else 4176) := rfl
  unfold noJumpInitializedState
  rw [expansion]
  by_cases empty : s.getReg .x16=0 <;>
    simp [MachineState.getReg] at empty <;>
    simp [noJumpSetupPrefix,noJumpSetupInstructions,execInstrBr,pc,signExtend21,signExtend13,
      signExtend12,MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc,empty] <;>
    first | rfl | (funext reg; cases reg <;> rfl)

theorem noJump_setup (s : MachineState) (pc : s.pc=4096) (fuel : Nat) (coins : Bool) :
    execute noJumpImage (9+fuel) s coins=
      (do let result ← execute noJumpImage fuel (noJumpInitializedState s) coins
          return result.charge 9 0) := by
  rw [←noJump_setup_same s pc]
  apply execute_unit_steps (states := noJumpSetupPrefix s)
  intro i hi
  refine ⟨.base ((noJumpSetupInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply noJump_fetch _ (if i<8 then i else 19) _ (by split <;> omega)
    · interval_cases i <;>
        simp [noJumpSetupPrefix,noJumpSetupInstructions,execInstrBr,pc,signExtend21,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
end CommitGolfCandidate.Compact
