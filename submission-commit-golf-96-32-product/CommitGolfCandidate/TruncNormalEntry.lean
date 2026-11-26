import CommitGolfCandidate.TruncDispatch
import CommitGolfCandidate.TruncSteps
import CommitGolfCandidate.Check
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 160000

theorem dispatchNormal (s : MachineState) (pc : s.pc=4096) (mode : s.getReg .x16≠128) :
    Runs (Trunc.wireImage true) s (checkDispatchState s) 7 7 := by
  have e : Trunc.dispatched s=checkDispatchState s := by
    unfold Trunc.dispatched checkDispatchState;rw [if_neg mode,if_neg mode];rfl
  intro f coins;rw [←e];exact Trunc.patchedDispatch s pc f coins

private def checkNormalLenInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x0 792]

private def checkNormalLenPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkNormalLenInstructions.take count).foldl execInstrBr state

private theorem check_normal_len_prefix (state : MachineState) (pc : state.pc = 4124)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (3 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel
            (checkNormalLenPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := checkNormalLenPrefix state)
  intro i hi
  refine ⟨.base ((checkNormalLenInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetchAt _ _ (7 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The normal length gate compares `x16 * 792` with `x17` (after dispatch with `x16 ≠ 128`). -/
def checkLengthState (state : MachineState) : MachineState :=
  ((checkNormalLenPrefix (checkDispatchState state) 3).setReg .x7 (state.getReg .x16 * 792)).setPC
    (if state.getReg .x16 * 792 = state.getReg .x17 then 4144 else 4432)

/-- For `x16 ≠ 128`, 12 instructions and 15 cycles reach the normal length decision. -/
theorem check_length_gate (state : MachineState) (pc : state.pc = 4096)
    (not128 : state.getReg .x16 ≠ 128) (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (12 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel
            (checkLengthState state) allowCoins
          return result.charge 15 0) := by
  let disp := checkDispatchState state
  have dispPC : disp.pc = 4124 := if_neg not128
  let ready := checkNormalLenPrefix disp 3
  let multiplied := (ready.setReg .x7 (state.getReg .x16 * 792)).setPC 4140
  have readyPC : ready.pc = 4136 := by
    simp [ready, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, dispPC, MachineState.setPC]
  have fetched₁ : fetch (Trunc.wireImage true) ready = some (.base (.MUL .x7 .x16 .x6)) := by
    apply fetchAt _ ready 10 _ (by decide) readyPC; rfl
  have fetched₂ : fetch (Trunc.wireImage true) multiplied = some (.base (.BNE .x7 .x17 292)) := by
    apply fetchAt _ multiplied 11 _ (by decide) rfl; rfl
  have readyCount : ready.getReg .x16 = state.getReg .x16 := by
    have h := (check_dispatch_registers state).2.2.2.2.2.1
    simpa [ready, disp, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC] using h
  have readyLength : ready.getReg .x17 = state.getReg .x17 := by
    have h := (check_dispatch_registers state).2.2.2.2.2.2.1
    simpa [ready, disp, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC] using h
  have readyFactor : ready.getReg .x6 = 792 := by
    dsimp only [ready, checkNormalLenPrefix, checkNormalLenInstructions, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step₁ : ordinaryStep ready (.base (.MUL .x7 .x16 .x6)) = some multiplied := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      readyCount, readyFactor, readyPC, multiplied]
    rfl
  have step₂ : ordinaryStep multiplied (.base (.BNE .x7 .x17 292)) = some (checkLengthState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, multiplied]
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17), readyLength]
    simp [checkLengthState, ready, disp, signExtend13, MachineState.setPC]
    split <;> simp_all
  rw [show 12 + fuel = 7 + (3 + (fuel + 2)) by omega,
    dispatchNormal state pc not128, check_normal_len_prefix disp dispPC]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched₁ step₁]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched₂ step₂]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- State at HALT, preserving all memory and all registers except the exit controls. -/
def checkExitState (state : MachineState) (success : Bool) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 (if success then 0 else 1)).setPC
    (if success then 4428 else 4440)

/-- Both exit blocks (`accept` at 4420, `reject` at 4432) halt in three cycles. -/
theorem check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 4420 else 4432) (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure, checkExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 4424 else 4436)
  have fetch₁ : fetch (Trunc.wireImage true) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply fetchAt _ state 84 _ (by decide) pc; rfl
    · apply fetchAt _ state 81 _ (by decide) pc; rfl
  have fetch₂ : fetch (Trunc.wireImage true) next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply fetchAt _ next 85 _ (by decide) rfl; rfl
    · apply fetchAt _ next 82 _ (by decide) rfl; rfl
  have fetch₃ : fetch (Trunc.wireImage true) (checkExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply fetchAt _ _ 86 _ (by decide) rfl; rfl
    · apply fetchAt _ _ 83 _ (by decide) rfl; rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, pc, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have step₂ : ordinaryStep next (.base (.ADDI .x10 .x0 (if success then 0 else 1))) =
      some (checkExitState state success) := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, checkExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, fetch₁, step₁, fetch₂, step₂, fetch₃, instructionCycles,
    bind_assoc, pure_bind]
  cases success <;> simp [checkExitState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

/-- A mismatching normal proof length is rejected in 15 instructions and 18 cycles. -/
theorem check_wrong_length (state : MachineState) (pc : state.pc = 4096)
    (not128 : state.getReg .x16 ≠ 128)
    (wrong : state.getReg .x16 * 792 ≠ state.getReg .x17)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (15 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkLengthState state) false, 18, 0⟩ := by
  have rejectPC : (checkLengthState state).pc = 4432 := if_neg wrong
  rw [show 15 + fuel = 12 + (3 + fuel) by omega, check_length_gate state pc not128,
    check_exit _ false rejectPC]
  simp [Execution.charge]

private def checkScratchInstructions : List Instr :=
  [.ADDI .x30 .x0 24, .ADDI .x21 .x0 256]

private def checkScratchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkScratchInstructions.take count).foldl execInstrBr state

/-- Valid normal lengths set `x30 = 24`, `x21 = 256`, and jump to `accept` (4420) if
empty or enter `check-position` (4156). -/
def checkReadyState (state : MachineState) : MachineState :=
  (checkScratchPrefix state 2).setPC (if state.getReg .x27 = 0 then 4420 else 4156)

private theorem check_scratch_prefix (state : MachineState) (pc : state.pc = 4144)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (2 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel
            (checkScratchPrefix state 2) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := checkScratchPrefix state)
  intro i hi
  refine ⟨.base ((checkScratchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetchAt _ _ (12 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The three-instruction transition after a valid normal length. -/
theorem check_ready (state : MachineState) (pc : state.pc = 4144)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.wireImage true) (3 + fuel) state allowCoins =
      (do let result ← execute (Trunc.wireImage true) fuel (checkReadyState state) allowCoins
          return result.charge 3 0) := by
  let ready := checkScratchPrefix state 2
  have readyPC : ready.pc = 4152 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x27 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have fetched : fetch (Trunc.wireImage true) ready = some (.base (.BEQ .x27 .x0 268)) := by
    apply fetchAt _ ready 14 _ (by decide) readyPC; rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 268)) = some (checkReadyState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show ready.getReg .x0 = 0 from rfl, readyPC]
    simp [checkReadyState, ready, signExtend13]
    split <;> simp_all
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, check_scratch_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- The normal length gate preserves the position count and all input memory. -/
theorem check_length_preserves (state : MachineState) :
    (checkLengthState state).getReg .x27 = state.getReg .x16 ∧
    (checkLengthState state).mem = state.mem := CommitGolfCandidate.check_length_preserves state

end CommitGolfCandidate.Trunc.Normal
