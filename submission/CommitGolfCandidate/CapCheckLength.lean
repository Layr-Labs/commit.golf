import CommitGolfCandidate.CapCheckLengthControl
import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.CapCheckExit

/-! The initial length gate compares bounded natural ABI lengths. A short
lower-record prefix rejects before any proof read or compression query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_check_multiplied_length (state : MachineState) :
    (capCheckMultiplied state).getReg .x17 = state.getReg .x17 ∧
    (capCheckMultiplied state).getReg .x7 = state.getReg .x16 * 576 := by
  constructor
  · simp only [capCheckMultiplied, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17)]
    exact (cap_check_setup_registers state).2.2.2.2.2.2.2.2
  · simp only [capCheckMultiplied, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0)]

theorem cap_check_length_decision (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    (capCheckLengthState (capProgram.initialState .check input)).pc =
      if input.proof.length < 576 * input.positions.card then 4808 else 4140 := by
  have control := cap_check_length_control (capProgram.initialState .check input)
  have required : ((capProgram.initialState .check input).getReg .x16 * 576).toNat =
      576 * input.positions.card := cap_check_required_length input
  have proofLength : ((capProgram.initialState .check input).getReg .x17).toNat =
      input.proof.length := by
    change (BitVec.ofNat 64 input.proof.length).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have bounded := (cap_check_loader_bounds input admitted).2.2
    omega
  simpa only [BitVec.lt_def, proofLength, required] using control

/-- Rejection uses fourteen actual instructions and seventeen cycles. -/
theorem cap_check_short_reject (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (short : input.proof.length < 576 * input.positions.card)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (14 + fuel)
      (capProgram.initialState .check input) allowCoins =
      pure ⟨.failure,
        capCheckExitState (capCheckLengthState (capProgram.initialState .check input)) false,
        17, 0⟩ := by
  have pc := cap_check_length_decision input admitted
  rw [if_pos short] at pc
  have gate : execute (capProgram.image .check) (11 + (3 + fuel))
      (capProgram.initialState .check input) allowCoins =
      (do let result ← execute (capProgram.image .check) (3 + fuel)
            (capCheckLengthState (capProgram.initialState .check input)) allowCoins
          return result.charge 14 0) :=
    cap_check_length_gate _ rfl (3 + fuel) allowCoins
  have exit : execute (capProgram.image .check) (3 + fuel)
      (capCheckLengthState (capProgram.initialState .check input)) allowCoins =
      pure ⟨.failure,
        capCheckExitState (capCheckLengthState (capProgram.initialState .check input)) false,
        3, 0⟩ := cap_check_exit _ false pc fuel allowCoins
  rw [show 14 + fuel = 11 + (3 + fuel) by omega, gate, exit]
  simp only [pure_bind, Execution.charge]

end CommitGolfCandidate
