import CommitGolfCandidate.CapCheckInputEntry

/-! The first checker record retains the actual ABI pointers and arbitrary
input memory. Workspace zero is inherited from the experimental loader, not
from a whole-state identification with the older checker image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSetupPrefix capCheckRecordEntry
  capCheckLengthState capCheckMultiplied

theorem cap_check_record_entry_register (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x21, .x9, .x18, .x19, .x31]) :
    (capCheckRecordEntry state).getReg reg = state.getReg reg :=
  by
    unfold capCheckRecordEntry
    exact (cap_check_constants_register _ 17 reg outside).trans MachineState.getReg_setPC

theorem cap_check_length_setup_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x7) :
    (capCheckLengthState state).getReg reg =
      (capCheckSetupPrefix state 9).getReg reg := by
  unfold capCheckLengthState
  rw [cap_flow_register]
  unfold capCheckMultiplied
  rw [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_check_initial_pointers (input : CheckInput) :
    let state := capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input))
    state.getReg .x26 = BitVec.ofNat 64 capProgram.layout.commitment ∧
    state.getReg .x24 = BitVec.ofNat 64 capProgram.layout.indices ∧
    state.getReg .x8 = BitVec.ofNat 64 capProgram.layout.values ∧
    state.getReg .x25 = BitVec.ofNat 64 capProgram.layout.proof ∧
    state.getReg .x27 = BitVec.ofNat 64 input.positions.card ∧
    state.getReg .x22 = BitVec.ofNat 64
      (capProgram.layout.proof + input.proof.length) := by
  dsimp only
  have registers := cap_check_setup_registers (capProgram.initialState .check input)
  repeat' constructor
  · rw [cap_check_record_entry_register _ .x26 (by decide),
      cap_check_length_setup_register _ .x26 (by decide), registers.1]
    rfl
  · rw [cap_check_record_entry_register _ .x24 (by decide),
      cap_check_length_setup_register _ .x24 (by decide), registers.2.1]
    rfl
  · rw [cap_check_record_entry_register _ .x8 (by decide),
      cap_check_length_setup_register _ .x8 (by decide), registers.2.2.1]
    rfl
  · rw [cap_check_record_entry_register _ .x25 (by decide),
      cap_check_length_setup_register _ .x25 (by decide), registers.2.2.2.1]
    rfl
  · rw [cap_check_record_entry_register _ .x27 (by decide), cap_check_input_count]
  · rw [cap_check_record_entry_register _ .x22 (by decide),
      cap_check_length_setup_register _ .x22 (by decide), registers.2.2.2.2.2.1]
    change BitVec.ofNat 64 capProgram.layout.proof + BitVec.ofNat 64 input.proof.length = _
    exact (BitVec.ofNat_add _ _).symm

theorem cap_check_initial_workspace_zero (input : CheckInput)
    (address : Nat) (bounded : address + 8 ≤ 32768) :
    (capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input))).getMem
      (BitVec.ofNat 64 address) = 0 := by
  have zero := cap_experimental_check_workspace_zero input address bounded
  simpa only [MachineState.getMem, cap_check_record_entry_memory,
    cap_check_length_memory] using zero

end CommitGolfCandidate
