import CommitGolfCandidate.NonceCompressedFetch
import CommitGolfCandidate.CapCheckExit

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_expanded_check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 4796 else 4808) (fuel : Nat) (allowCoins : Bool) :
    execute nonceExpandedImage (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure,
        capCheckExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 4800 else 4812)
  have first : fetch nonceExpandedImage state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply cap_image_fetch _ state 178 _ (by decide) pc
      rfl
    · apply cap_image_fetch _ state 175 _ (by decide) pc
      rfl
  have second : fetch nonceExpandedImage next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply cap_image_fetch _ next 179 _ (by decide) rfl
      rfl
    · apply cap_image_fetch _ next 176 _ (by decide) rfl
      rfl
  have last : fetch nonceExpandedImage (capCheckExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply cap_image_fetch _ _ 180 _ (by decide) rfl
      rfl
    · apply cap_image_fetch _ _ 177 _ (by decide) rfl
      rfl
  have stepFirst : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, pc, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have stepSecond : ordinaryStep next (.base (.ADDI .x10 .x0 (if success then 0 else 1))) =
      some (capCheckExitState state success) := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, capCheckExitState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, first, stepFirst, second, stepSecond, last, instructionCycles,
    bind_assoc, pure_bind]
  cases success <;> simp [capCheckExitState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

end CommitGolfCandidate
