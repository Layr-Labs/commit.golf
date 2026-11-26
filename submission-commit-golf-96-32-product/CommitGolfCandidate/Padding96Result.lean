import CommitGolfCandidate.Padding96

/-! Normalize the adapter's final machine state to its externally visible effect. -/
set_option maxHeartbeats 2000000

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem set_pc_self (state : MachineState) : state.setPC state.pc = state := by
  cases state
  rfl

theorem padding_finished (caller : MachineState) (entry : Word) (answer : BitVec 256)
    (alignedReturn : (caller.pc+4) &&& ~~~1 = caller.pc+4)
    (separate : ∀ word < 4, ∀ byte < 32,
      caller.getReg .x10+BitVec.ofNat 64 (64+8*word) ≠
        alignToDword (caller.getReg .x12+BitVec.ofNat 64 byte)) :
    paddingFinishPrefix
      (writeBits
        (paddingSetupPrefix ((caller.setReg .x31 (caller.pc+4)).setPC entry) 9)
        (caller.getReg .x12) answer) 6 =
      paddedCompressionState caller answer := by
  let linked := caller.setReg .x31 (caller.pc+4)
  let saved := savePaddingRegisters linked
  let source := caller.getReg .x10
  let destination := caller.getReg .x12
  let written := writeBits (padMemory saved source) destination answer
  have ready : paddingSetupPrefix (linked.setPC entry) 9 =
      ((padMemory saved source).setReg .x11 96).setPC (entry+36) := by
    rw [padding_setup_shape]
    rfl
  have padReg (state : MachineState) (source : Word) (reg : Reg) :
      (padMemory state source).getReg reg = state.getReg reg := by cases reg <;> rfl
  have sourceReg : written.getReg .x10 = source := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, source,
      MachineState.getReg, MachineState.setReg]
  have saved14 : written.getReg .x14 = caller.getMem (source+64) := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, source,
      MachineState.getReg, MachineState.setReg, MachineState.getMem]
  have saved15 : written.getReg .x15 = caller.getMem (source+72) := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, source,
      MachineState.getReg, MachineState.setReg, MachineState.getMem]
  have saved16 : written.getReg .x16 = caller.getMem (source+80) := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, source,
      MachineState.getReg, MachineState.setReg, MachineState.getMem]
  have saved17 : written.getReg .x17 = caller.getMem (source+88) := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, source,
      MachineState.getReg, MachineState.setReg, MachineState.getMem]
  have link : written.getReg .x31 = caller.pc+4 := by
    refine (writeBits_register (padMemory saved source) destination answer _).trans ?_
    rw [padReg]
    simp [saved, linked, savePaddingRegisters, MachineState.getReg, MachineState.setReg]
  have finishShape :
      paddingFinishPrefix ((written.setReg .x11 96).setPC (entry+36+4)) 6 =
        ((restorePadding written caller source).setReg .x11 64).setPC (caller.pc+4) := by
    rw [padding_finish_shape]
    simp only [MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x10),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x14),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x15),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x16),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x17),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x31),
      sourceReg, saved14, saved15, saved16, saved17, link, alignedReturn]
    simp only [restorePadding, MachineState.setReg, MachineState.setMem, MachineState.setPC]
    congr 1
    funext reg
    cases reg <;> rfl
  change paddingFinishPrefix (writeBits (paddingSetupPrefix (linked.setPC entry) 9)
    destination answer) 6 = _
  rw [ready, write_bits_set_pc, write_bits_set_reg, finishShape]
  have restore : restorePadding written caller source = restorePadding written saved source := rfl
  rw [restore, restore_padding_write saved source destination answer separate]
  rw [paddedCompressionState, write_bits_set_reg]
  let result := (writeBits saved destination answer).setReg .x11 64
  have resultPC : result.pc = caller.pc+4 := by
    rw [MachineState.pc_setReg]
    rfl
  exact (congrArg (fun pc => result.setPC pc) resultPC.symm).trans (set_pc_self result)

end CommitGolfCandidate
