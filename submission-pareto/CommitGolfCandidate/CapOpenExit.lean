import CommitGolfCandidate.CapOpenDfsRun

/-! Actual four-instruction opening epilogue. The reported byte length is the
cursor displacement from the ABI output base. Natural subtraction equality is
proved only under explicit nonwrapping bounds. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenLengthState (state : MachineState) : MachineState :=
  (state.setReg .x11 (state.getReg .x25 - state.getReg .x15)).setPC 4528

def capOpenExitState (state : MachineState) : MachineState :=
  (((capOpenLengthState state).setReg .x5 1).setReg .x10 0).setPC 4536

theorem cap_open_exit (state : MachineState)
    (pc : state.pc = capAdvanceDone false) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage false) (4 + fuel) state allowCoins =
      pure ⟨.success, capOpenExitState state, 4, 0⟩ := by
  let second := (capOpenLengthState state).setReg .x5 1 |>.setPC 4532
  have firstFetch : fetch (capWalkImage false) state = some (.base (.SUB .x11 .x25 .x15)) := by
    apply cap_image_fetch _ state 107 _ (by decide) pc
    rfl
  have secondFetch : fetch (capWalkImage false) (capOpenLengthState state) =
      some (.base (.ADDI .x5 .x0 1)) := by
    apply cap_image_fetch _ _ 108 _ (by decide) rfl
    rfl
  have thirdFetch : fetch (capWalkImage false) second =
      some (.base (.ADDI .x10 .x0 0)) := by
    apply cap_image_fetch _ _ 109 _ (by decide) rfl
    rfl
  have lastFetch : fetch (capWalkImage false) (capOpenExitState state) =
      some (.base .ECALL) := by
    apply cap_image_fetch _ _ 110 _ (by decide) rfl
    rfl
  have first : ordinaryStep state (.base (.SUB .x11 .x25 .x15)) =
      some (capOpenLengthState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, capOpenLengthState,
      pc, capAdvanceDone]
  have secondStep : ordinaryStep (capOpenLengthState state) (.base (.ADDI .x5 .x0 1)) =
      some second := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      second, capOpenLengthState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have third : ordinaryStep second (.base (.ADDI .x10 .x0 0)) =
      some (capOpenExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      second, capOpenExitState, capOpenLengthState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 4 fuel]
  simp only [execute, firstFetch, first, secondFetch, secondStep, thirdFetch, third,
    lastFetch, instructionCycles, bind_assoc, pure_bind]
  simp [capOpenExitState, capOpenLengthState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

theorem cap_open_exit_report (state : MachineState) (base bytes : Nat)
    (start : state.getReg .x15 = BitVec.ofNat 64 base)
    (finish : state.getReg .x25 = BitVec.ofNat 64 (base + bytes))
    (noWrap : base + bytes < 2^64) :
    ((capOpenExitState state).getReg .x11).toNat = bytes := by
  have report : (capOpenExitState state).getReg .x11 =
      state.getReg .x25 - state.getReg .x15 := by
    simp [capOpenExitState, capOpenLengthState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  rw [report, finish, start, BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem cap_open_exit_memory (state : MachineState) :
    (capOpenExitState state).mem = state.mem := rfl

end CommitGolfCandidate
