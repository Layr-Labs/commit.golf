import CommitGolfCandidate.NonceCompressedFetch

/-! Actual four-instruction compacting opening epilogue. The reported byte length is the
cursor displacement from the ABI output base. Natural subtraction equality is
proved only under explicit nonwrapping bounds. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def nonceCompactLengthState (state : MachineState) : MachineState :=
  (state.setReg .x11 (state.getReg .x25 - state.getReg .x15)).setPC 5132

def nonceCompactExitState (state : MachineState) : MachineState :=
  (((nonceCompactLengthState state).setReg .x5 1).setReg .x10 0).setPC 5140

theorem nonce_compact_exit (state : MachineState)
    (pc : state.pc = 5128) (fuel : Nat) (allowCoins : Bool) :
    execute nonceCompactImage (4 + fuel) state allowCoins =
      pure ⟨.success, nonceCompactExitState state, 4, 0⟩ := by
  let second := (nonceCompactLengthState state).setReg .x5 1 |>.setPC 5136
  have firstFetch : fetch nonceCompactImage state = some (.base (.SUB .x11 .x25 .x15)) := by
    apply cap_image_fetch _ state 258 _ (by decide) pc
    rfl
  have secondFetch : fetch nonceCompactImage (nonceCompactLengthState state) =
      some (.base (.ADDI .x5 .x0 1)) := by
    apply cap_image_fetch _ _ 259 _ (by decide) rfl
    rfl
  have thirdFetch : fetch nonceCompactImage second =
      some (.base (.ADDI .x10 .x0 0)) := by
    apply cap_image_fetch _ _ 260 _ (by decide) rfl
    rfl
  have lastFetch : fetch nonceCompactImage (nonceCompactExitState state) =
      some (.base .ECALL) := by
    apply cap_image_fetch _ _ 261 _ (by decide) rfl
    rfl
  have first : ordinaryStep state (.base (.SUB .x11 .x25 .x15)) =
      some (nonceCompactLengthState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, nonceCompactLengthState,
      pc]
  have secondStep : ordinaryStep (nonceCompactLengthState state) (.base (.ADDI .x5 .x0 1)) =
      some second := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      second, nonceCompactLengthState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have third : ordinaryStep second (.base (.ADDI .x10 .x0 0)) =
      some (nonceCompactExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      second, nonceCompactExitState, nonceCompactLengthState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 4 fuel]
  simp only [execute, firstFetch, first, secondFetch, secondStep, thirdFetch, third,
    lastFetch, instructionCycles, bind_assoc, pure_bind]
  simp [nonceCompactExitState, nonceCompactLengthState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

theorem nonce_compact_exit_report (state : MachineState) (base bytes : Nat)
    (start : state.getReg .x15 = BitVec.ofNat 64 base)
    (finish : state.getReg .x25 = BitVec.ofNat 64 (base + bytes))
    (noWrap : base + bytes < 2^64) :
    ((nonceCompactExitState state).getReg .x11).toNat = bytes := by
  have report : (nonceCompactExitState state).getReg .x11 =
      state.getReg .x25 - state.getReg .x15 := by
    simp [nonceCompactExitState, nonceCompactLengthState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  rw [report, finish, start, BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem nonce_compact_exit_memory (state : MachineState) :
    (nonceCompactExitState state).mem = state.mem := rfl

end CommitGolfCandidate
