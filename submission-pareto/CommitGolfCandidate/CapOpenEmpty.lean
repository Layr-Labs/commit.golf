import CommitGolfCandidate.CapOpenSetup
import CommitGolfCandidate.CapOpenExit

/-! Empty requests use the actual setup branch and halt with zero proof bytes,
zero public queries and unchanged memory. They never enter record, mark or DFS
code, so the standalone all-unknown cap codec is not used for this case. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_empty_execute (state : MachineState)
    (pc : state.pc = 4096) (empty : state.getReg .x16 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening) (33+fuel) state allowCoins =
      pure ⟨.success, capOpenExitState (capOpenInitializedState state), 33, 0⟩ := by
  have donePC : (capOpenInitializedState state).pc = capAdvanceDone false := by
    simp only [capOpenInitializedState, empty, ↓reduceIte, MachineState.setPC]
    rfl
  rw [show 33+fuel = 29+(4+fuel) by omega, cap_open_setup_execute state pc]
  have exit : execute (capProgram.image .opening) (4+fuel)
      (capOpenInitializedState state) allowCoins =
      pure ⟨.success, capOpenExitState (capOpenInitializedState state), 4, 0⟩ :=
    cap_open_exit (capOpenInitializedState state) donePC fuel allowCoins
  rw [exit]
  simp only [pure_bind, Execution.charge, Nat.zero_add]

theorem cap_open_empty_report (state : MachineState) :
    (capOpenExitState (capOpenInitializedState state)).getReg .x11 = 0 := by
  have regs := cap_open_setup_registers state
  have pointer := regs.2.2.1
  have base := regs.2.2.2.2.2.2.2.2.2.1
  simp only [capOpenExitState, capOpenLengthState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x11),
    MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0), pointer, base,
    BitVec.sub_self]
  rfl

theorem cap_open_empty_memory (state : MachineState) :
    (capOpenExitState (capOpenInitializedState state)).mem = state.mem := by
  rw [cap_open_exit_memory, cap_open_setup_memory]

end CommitGolfCandidate
