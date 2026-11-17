import CommitGolfCandidate.CapCheckConstantsFrame
import CommitGolfCandidate.CapCheckEmpty

/-! The nonempty branch and workspace initialization form the checked entry
to the first record. Empty requests instead use the already proved real halt.
Neither path reads the proof or performs a compression query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckSetupPrefix capCheckConstantsPrefix

def capCheckRecordEntry (state : MachineState) : MachineState :=
  capCheckConstantsPrefix (state.setPC 4144) 17

theorem cap_check_start_nonempty (state : MachineState) (pc : state.pc = 4140)
    (nonempty : state.getReg .x27 ≠ 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (18 + fuel) state allowCoins =
      (do let result ← execute (capProgram.image .check) fuel
            (capCheckRecordEntry state) allowCoins
          return result.charge 18 0) := by
  have fetched : fetch (capProgram.image .check) state =
      some (.base (.BEQ .x27 .x0 652)) := by
    apply cap_image_fetch _ state 11 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.BEQ .x27 .x0 652)) =
      some (state.setPC 4144) := by
    have nonzero : state.regs .x27 ≠ 0#64 := nonempty
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      MachineState.getReg, MachineState.setPC, pc, nonzero]
  have initialized : execute (capProgram.image .check) (17 + fuel)
      (state.setPC 4144) allowCoins =
      (do let result ← execute (capProgram.image .check) fuel
            (capCheckRecordEntry state) allowCoins
          return result.charge 17 0) :=
    cap_check_constants_execute _ rfl fuel allowCoins
  rw [show 18 + fuel = (17 + fuel) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped, initialized]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem cap_check_length_count (state : MachineState) :
    (capCheckLengthState state).getReg .x27 = state.getReg .x16 := by
  rw [capCheckLengthState, cap_flow_register]
  simp only [capCheckMultiplied, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x27)]
  exact (cap_check_setup_registers state).2.2.2.2.1

theorem cap_check_length_proof_length (state : MachineState) :
    (capCheckLengthState state).getReg .x17 = state.getReg .x17 := by
  rw [capCheckLengthState, cap_flow_register]
  exact (cap_check_multiplied_registers state).1

theorem cap_check_record_entry_pc (state : MachineState) :
    (capCheckRecordEntry state).pc = 4212 :=
  cap_check_constants_finished_pc _ rfl

theorem cap_check_record_entry_memory (state : MachineState) :
    (capCheckRecordEntry state).mem = state.mem :=
  cap_check_constants_memory _

end CommitGolfCandidate
