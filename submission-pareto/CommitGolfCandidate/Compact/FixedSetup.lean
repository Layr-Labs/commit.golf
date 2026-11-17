import CommitGolfCandidate.Compact.FixedImage
/-! Checked entry sequence and empty-opening branch for the unrolled image.
The register setup agrees with the existing reference execution. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixedSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0,.ADDI .x24 .x13 0,.ADDI .x25 .x15 0,.ADDI .x27 .x16 0,
   .LUI .x19 4096,.LUI .x6 262144,.ADD .x18 .x9 .x6,.JAL .x0 48,
   .BEQ .x27 .x0 1228]
def fixedSetupPrefix (s : MachineState) (count : Nat) : MachineState :=
  (fixedSetupInstructions.take count).foldl execInstrBr s

def fixedInitializedState (s : MachineState) : MachineState :=
  (openingInitializedState s).setPC (if s.getReg .x16=0 then 5400 else 4176)

theorem fixed_setup_same (s : MachineState) (pc : s.pc=4096) :
    fixedSetupPrefix s 9=fixedInitializedState s := by
  have expansion (s : MachineState) : openingInitializedState s=
      (([.ADDI .x9 .x12 0,.ADDI .x24 .x13 0,.ADDI .x25 .x15 0,.ADDI .x27 .x16 0,
        .ADDI .x19 .x0 0,.SLLI .x19 .x19 11,.ADDI .x19 .x19 4,
        .SLLI .x19 .x19 11,.ADDI .x19 .x19 0,.SLLI .x19 .x19 11,.ADDI .x19 .x19 0,
        .ADDI .x6 .x0 0,.SLLI .x6 .x6 11,.ADDI .x6 .x6 256,
        .SLLI .x6 .x6 11,.ADDI .x6 .x6 0,.SLLI .x6 .x6 11,.ADDI .x6 .x6 0,
        .ADD .x18 .x9 .x6] : List Instr).foldl execInstrBr s).setPC
        (if s.getReg .x16=0 then 4320 else 4176) := rfl
  unfold fixedInitializedState
  rw [expansion]
  by_cases empty : s.getReg .x16=0 <;>
    simp [MachineState.getReg] at empty <;>
    simp [fixedSetupPrefix,fixedSetupInstructions,execInstrBr,pc,signExtend21,signExtend13,
      signExtend12,MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc,empty] <;>
    first | rfl | (funext reg; cases reg <;> rfl)

theorem fixed_setup (s : MachineState) (pc : s.pc=4096) (fuel : Nat) (coins : Bool) :
    execute fixedImage (9+fuel) s coins=
      (do let result ← execute fixedImage fuel (fixedInitializedState s) coins
          return result.charge 9 0) := by
  rw [←fixed_setup_same s pc]
  apply execute_unit_steps (states := fixedSetupPrefix s)
  intro i hi
  refine ⟨.base ((fixedSetupInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply fixed_fetch _ (if i<8 then i else 19) _ (by split <;> omega)
    · interval_cases i <;>
        simp [fixedSetupPrefix,fixedSetupInstructions,execInstrBr,pc,signExtend21,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
end CommitGolfCandidate.Compact
