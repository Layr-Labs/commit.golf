import CommitGolfCandidate.CapCheckSaltReference
import CommitGolfCandidate.CapMemoryFrame

/-! The record salt macro changes only the loaded index, scratch load
register and proof cursor. Its scratch writes preserve the actual high input
buffers and the separate low cap-root and mark arrays. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSaltLoadedState capCheckSaltCopiedState

theorem cap_check_salt_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x20, .x6, .x25]) :
    (capCheckSaltState state).getReg reg = state.getReg reg := by
  have not20 : reg ≠ .x20 := by simp_all
  have not6 : reg ≠ .x6 := by simp_all
  have not25 : reg ≠ .x25 := by simp_all
  unfold capCheckSaltState
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not25)]
  unfold capCheckSaltCopiedState
  rw [cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) reg not6,
    cap_check_salt_loaded_register state reg not20]

theorem cap_check_salt_cursor (state : MachineState) :
    (capCheckSaltState state).getReg .x25 = state.getReg .x25 + 32 := by
  unfold capCheckSaltState
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0)]
  unfold capCheckSaltCopiedState
  rw [cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) .x25 (by decide),
    cap_check_salt_loaded_register state .x25 (by decide)]
  rfl

theorem cap_check_salt_index (state : MachineState) :
    (capCheckSaltState state).getReg .x20 = state.getMem (state.getReg .x24) := by
  unfold capCheckSaltState
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x20)]
  unfold capCheckSaltCopiedState
  rw [cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) .x20 (by decide)]
  unfold capCheckSaltLoadedState
  simp only [execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0),
    show signExtend12 (0 : BitVec 12) = (0 : Word) by rfl]
  change state.getMem (state.getReg .x24 + (0#64)) = _
  rw [BitVec.add_zero]

theorem cap_check_salt_pc (state : MachineState) (pc : state.pc = 4212) :
    (capCheckSaltState state).pc = 4252 := by
  unfold capCheckSaltState
  simp only [execInstrBr, MachineState.setPC]
  rw [capCheckSaltCopiedState, cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide),
    cap_check_salt_loaded_pc state pc]
  rfl

theorem cap_check_salt_high_frame (state reference : MachineState)
    (scratch : state.getReg .x21 = 256) (frame : CapHighBytes state reference) :
    CapHighBytes (capCheckSaltState state) reference := by
  intro address lower upper
  have distinct : ∀ i < 4,
      BitVec.ofNat 64 (8 * (address / 8)) ≠ BitVec.ofNat 64 (256 + 8*i) := by
    intro i inside equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : 256 + 8*i < 2^64)] at numeric
    omega
  have word := cap_check_salt_outside state
    (BitVec.ofNat 64 (8 * (address / 8))) scratch distinct
  have finishedByte := aligned_byte (capCheckSaltState state)
    (address / 8) (address % 8) (by omega)
  have stateByte := aligned_byte state (address / 8) (address % 8) (by omega)
  have decomp : 8 * (address / 8) + address % 8 = address := by omega
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8),
    decomp] at finishedByte stateByte
  rw [finishedByte, word, ← stateByte]
  exact frame address lower upper

end CommitGolfCandidate
