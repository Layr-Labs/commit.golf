import CommitGolfCandidate.CapCheckSetup

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSetupPrefix

theorem cap_check_multiplied_registers (state : MachineState) :
    (capCheckMultiplied state).getReg .x17 = state.getReg .x17 ∧
    (capCheckMultiplied state).getReg .x7 = state.getReg .x16 * 544 := by
  constructor
  · simp only [capCheckMultiplied, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17)]
    exact (cap_check_setup_registers state).2.2.2.2.2.2.2.2
  · simp only [capCheckMultiplied, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0)]

theorem cap_check_multiplied_pc (state : MachineState) :
    (capCheckMultiplied state).pc = 4136 := rfl

theorem cap_check_length_control (state : MachineState) :
    (capCheckLengthState state).pc =
      if state.getReg .x17 < state.getReg .x16 * 544 then 4808 else 4140 := by
  rw [capCheckLengthState, cap_flow_below_pc]
  have regs := cap_check_multiplied_registers state
  simp only [regs.1, regs.2, cap_check_multiplied_pc]
  split <;> rfl

end CommitGolfCandidate
