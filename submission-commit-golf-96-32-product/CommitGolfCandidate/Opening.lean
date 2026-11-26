import CommitGolfCandidate.Execution
import CommitGolfCandidate.HeapLayout

/-! Control-flow proofs for the concrete opening image (16-byte salts + level-7 cap table
for `k = 128`, 784 B/pos otherwise). Instruction addresses below are checked against the
submitted bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem opening_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 97) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .opening).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .opening) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .opening).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

/-- The nineteen straight-line instructions before the initial empty-opening test. -/
private def openingSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0, .ADDI .x24 .x13 0, .ADDI .x25 .x15 0, .ADDI .x27 .x16 0,
   .ADDI .x19 .x0 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 4,
   .SLLI .x19 .x19 11, .ADDI .x19 .x19 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 0,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 384,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x18 .x9 .x6]

private def openingSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSetupInstructions.take count).foldl execInstrBr state

/-- Execution of setup is checked against every corresponding instruction encoding. -/
private theorem opening_setup_prefix (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (19 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSetupPrefix state 19) allowCoins
          return result.charge 19 0) := by
  apply execute_unit_steps (states := openingSetupPrefix state)
  intro i hi
  refine ⟨.base ((openingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after initial pointer setup and empty-opening branch (`open-done` at 4312,
or depth selection at 4176). -/
def openingInitializedState (state : MachineState) : MachineState :=
  (openingSetupPrefix state 19).setPC
    (if state.getReg .x16 = 0 then 4312 else 4176)

/-- Setup copies the ABI pointers and count, and computes the heap size and salt base.
The original position count and all input memory are preserved. -/
theorem opening_setup_registers (state : MachineState) :
    (openingInitializedState state).getReg .x9 = state.getReg .x12 ∧
    (openingInitializedState state).getReg .x24 = state.getReg .x13 ∧
    (openingInitializedState state).getReg .x25 = state.getReg .x15 ∧
    (openingInitializedState state).getReg .x27 = state.getReg .x16 ∧
    (openingInitializedState state).getReg .x19 = 16777216 ∧
    (openingInitializedState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (openingInitializedState state).getReg .x16 = state.getReg .x16 ∧
    (openingInitializedState state).mem = state.mem := by
  dsimp only [openingInitializedState, openingSetupPrefix, openingSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

/-- Exact twenty-cycle setup from the actual image entry point. -/
theorem opening_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (20 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingInitializedState state) allowCoins
          return result.charge 20 0) := by
  let ready := openingSetupPrefix state 19
  have readyPC : ready.pc = 4172 := by
    simp [ready, openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x16 := by
    simpa only [openingInitializedState, MachineState.getReg_setPC] using
      (opening_setup_registers state).2.2.2.1
  have fetched : fetch (submission.image .opening) ready =
      some (.base (.BEQ .x27 .x0 140)) := by
    apply opening_fetch ready 19 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 140)) =
      some (openingInitializedState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show ready.getReg .x0 = 0 from rfl, readyPC]
    simp [openingInitializedState, ready, signExtend13]
    split <;> simp_all
  rw [show 20 + fuel = 19 + (fuel + 1) by omega, opening_setup_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- State after selecting path depth (`17` when `x27 = 128`, `24` otherwise) and
reaching `open-position` at PC 4192. -/
def openingDepthState (state : MachineState) : MachineState :=
  if state.getReg .x27 = 128 then
    (((state.setReg .x30 24).setReg .x6 128).setReg .x30 17).setPC 4192
  else
    ((state.setReg .x30 24).setReg .x6 128).setPC 4192

theorem opening_depth_register (state : MachineState) (reg : Reg)
    (not6 : reg ≠ .x6) (not30 : reg ≠ .x30) :
    (openingDepthState state).getReg reg = state.getReg reg := by
  unfold openingDepthState
  split <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not30),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not6)]

theorem opening_depth_value (state : MachineState) :
    (openingDepthState state).getReg .x30 =
      if state.getReg .x27 = 128 then 17 else 24 := by
  unfold openingDepthState
  split <;> simp [MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

theorem opening_depth_pc (state : MachineState) :
    (openingDepthState state).pc = 4192 := by
  unfold openingDepthState; split <;> rfl

theorem opening_depth_memory (state : MachineState) :
    (openingDepthState state).mem = state.mem := by
  unfold openingDepthState; split <;> rfl

/-- Selecting path depth takes 4 cycles when `x27 = 128` and 3 cycles otherwise. -/
theorem opening_depth_select (state : MachineState) (pc : state.pc = 4176)
    (fuel : Nat) (allowCoins : Bool) :
    let cost := if state.getReg .x27 = 128 then 4 else 3
    execute (submission.image .opening) (cost + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingDepthState state) allowCoins
          return result.charge cost 0) := by
  let s1 := (state.setReg .x30 24).setPC 4180
  let s2 := ((state.setReg .x30 24).setReg .x6 128).setPC 4184
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x30 .x0 24)) := by
    apply opening_fetch state 20 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) s1 = some (.base (.ADDI .x6 .x0 128)) := by
    apply opening_fetch s1 21 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .opening) s2 = some (.base (.BNE .x27 .x6 8)) := by
    apply opening_fetch s2 22 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x30 .x0 24)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st1 : ordinaryStep s1 (.base (.ADDI .x6 .x0 128)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  by_cases cap : state.getReg .x27 = 128
  · simp only [cap, ↓reduceIte, openingDepthState]
    have capR : state.regs .x27 = 128 := by simpa [MachineState.getReg] using cap
    let s3 := ((state.setReg .x30 24).setReg .x6 128).setPC 4188
    have st2 : ordinaryStep s2 (.base (.BNE .x27 .x6 8)) = some s3 := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s2, s3,
        capR, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    have f3 : fetch (submission.image .opening) s3 = some (.base (.ADDI .x30 .x0 17)) := by
      apply opening_fetch s3 23 _ (by decide) rfl; rfl
    have st3 : ordinaryStep s3 (.base (.ADDI .x30 .x0 17)) =
        some ((((state.setReg .x30 24).setReg .x6 128).setReg .x30 17).setPC 4192) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s3,
        MachineState.getReg, MachineState.setReg, MachineState.setPC]
    rw [show 4 + fuel = (((fuel + 1) + 1) + 1) + 1 by omega]
    rw [execute_ordinary_step _ _ _ _ _ _ f0 st0,
      execute_ordinary_step _ _ _ _ _ _ f1 st1,
      execute_ordinary_step _ _ _ _ _ _ f2 st2,
      execute_ordinary_step _ _ _ _ _ _ f3 st3]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]
  · simp only [cap, ↓reduceIte, openingDepthState]
    have capR : state.regs .x27 ≠ 128 := by simpa [MachineState.getReg] using cap
    have st2 : ordinaryStep s2 (.base (.BNE .x27 .x6 8)) =
        some (((state.setReg .x30 24).setReg .x6 128).setPC 4192) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s2,
        MachineState.getReg, MachineState.setReg, MachineState.setPC]
      exact capR
    rw [show 3 + fuel = ((fuel + 1) + 1) + 1 by omega]
    rw [execute_ordinary_step _ _ _ _ _ _ f0 st0,
      execute_ordinary_step _ _ _ _ _ _ f1 st1,
      execute_ordinary_step _ _ _ _ _ _ f2 st2]
    simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- The path-loop latch really is a decrement followed by a backward BNE. -/
private theorem opening_fetch_decrement (state : MachineState)
    (pc : state.pc = 4292) :
    fetch (submission.image .opening) state = some (.base (.ADDI .x28 .x28 4095)) := by
  apply opening_fetch state 49 _ (by decide) pc
  rfl

private theorem opening_fetch_branch (state : MachineState)
    (pc : state.pc = 4296) :
    fetch (submission.image .opening) state = some (.base (.BNE .x28 .x0 8128)) := by
  apply opening_fetch state 50 _ (by decide) pc
  rfl

/-- State after the inner loop's two-instruction latch. Counter zero exits to
`open-next` (4300); a nonzero counter branches back to `open-path` (4232). -/
def openingLatchState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x28 - 1
  (state.setReg .x28 remaining).setPC (if remaining = 0 then 4300 else 4232)

/-- Exact interpreter behavior of the loop latch, with arbitrary memory and coins. -/
theorem opening_latch (state : MachineState) (pc : state.pc = 4292)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingLatchState state) allowCoins
          return result.charge 2 0) := by
  have first := opening_fetch_decrement state pc
  let next := (state.setReg .x28 (state.getReg .x28 - 1)).setPC 4296
  have second := opening_fetch_branch next rfl
  have step : ordinaryStep state (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have branch : ordinaryStep next (.base (.BNE .x28 .x0 8128)) =
      some (openingLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, openingLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, first, step, second, branch, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The outer loop advances the index pointer and decrements the position count. -/
def openingNextState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x27 - 1
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 remaining).setPC
    (if remaining = 0 then 4312 else 4192)

/-- Exact three-instruction transition from `open-next` (4300) to `open-position` (4192)
or `open-done` (4312). -/
theorem opening_next (state : MachineState) (pc : state.pc = 4300)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingNextState state) allowCoins
          return result.charge 3 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x24 .x24 8)) := by
    apply opening_fetch state 51 _ (by decide) pc
    rfl
  let advanced := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4304
  let next := (advanced.setReg .x27 (state.getReg .x27 - 1)).setPC 4308
  have second : fetch (submission.image .opening) advanced =
      some (.base (.ADDI .x27 .x27 4095)) := by
    apply opening_fetch advanced 52 _ (by decide) rfl
    rfl
  have third : fetch (submission.image .opening) next =
      some (.base (.BNE .x27 .x0 8076)) := by
    apply opening_fetch next 53 _ (by decide) rfl
    rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, pc]
  have step₂ : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, next, BitVec.sub_eq_add_neg, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  have step₃ : ordinaryStep next (.base (.BNE .x27 .x0 8076)) =
      some (openingNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, openingNextState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, first, step₁, second, step₂, third, step₃, instructionCycles,
    bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Dispatch at `open-done` (4312): `x16 = 128` falls through to cap copy (4320);
otherwise branch to normal exit (4456). -/
def openingDoneGateState (state : MachineState) : MachineState :=
  (state.setReg .x6 128).setPC (if state.getReg .x16 = 128 then 4320 else 4456)

theorem opening_done_gate (state : MachineState) (pc : state.pc = 4312)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingDoneGateState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x6 128).setPC 4316
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x6 .x0 128)) := by
    apply opening_fetch state 54 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) next = some (.base (.BNE .x16 .x6 140)) := by
    apply opening_fetch next 55 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x6 .x0 128)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s1 : ordinaryStep next (.base (.BNE .x16 .x6 140)) = some (openingDoneGateState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, next,
      openingDoneGateState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Final machine state for normal exit (`k ≠ 128`), reporting `784 * k` proof bytes. -/
def openingExitState (state : MachineState) : MachineState :=
  ((((state.setReg .x6 784).setReg .x11 (state.getReg .x16 * 784)).setReg .x5 1).setReg
    .x10 0).setPC 4480

/-- The normal return block (4456) halts successfully, reports 784 bytes per position,
and costs exactly ten cycles (including the four-cycle multiplication). -/
theorem opening_exit (state : MachineState) (pc : state.pc = 4456)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (7 + fuel) state allowCoins =
      pure ⟨.success, openingExitState state, 10, 0⟩ := by
  let s₁ := (state.setReg .x6 0).setPC 4460
  let s₂ := (state.setReg .x6 0).setPC 4464
  let s₃ := (state.setReg .x6 784).setPC 4468
  let s₄ := ((state.setReg .x6 784).setReg .x11 (state.getReg .x16 * 784)).setPC 4472
  let s₅ := (((state.setReg .x6 784).setReg .x11 (state.getReg .x16 * 784)).setReg
    .x5 1).setPC 4476
  let s₆ := openingExitState state
  have fetch0 : fetch (submission.image .opening) state =
      some (.base (.ADDI .x6 .x0 0)) := by
    apply opening_fetch state 90 _ (by decide) pc; rfl
  have fetch1 : fetch (submission.image .opening) s₁ =
      some (.base (.SLLI .x6 .x6 11)) := by
    apply opening_fetch s₁ 91 _ (by decide) rfl; rfl
  have fetch2 : fetch (submission.image .opening) s₂ =
      some (.base (.ADDI .x6 .x6 784)) := by
    apply opening_fetch s₂ 92 _ (by decide) rfl; rfl
  have fetch3 : fetch (submission.image .opening) s₃ =
      some (.base (.MUL .x11 .x16 .x6)) := by
    apply opening_fetch s₃ 93 _ (by decide) rfl; rfl
  have fetch4 : fetch (submission.image .opening) s₄ =
      some (.base (.ADDI .x5 .x0 1)) := by
    apply opening_fetch s₄ 94 _ (by decide) rfl; rfl
  have fetch5 : fetch (submission.image .opening) s₅ =
      some (.base (.ADDI .x10 .x0 0)) := by
    apply opening_fetch s₅ 95 _ (by decide) rfl; rfl
  have fetch6 : fetch (submission.image .opening) s₆ =
      some (.base .ECALL) := by
    apply opening_fetch s₆ 96 _ (by decide) rfl; rfl
  have step0 : ordinaryStep state (.base (.ADDI .x6 .x0 0)) = some s₁ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₁, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp [pc]
  have step1 : ordinaryStep s₁ (.base (.SLLI .x6 .x6 11)) = some s₂ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₁, s₂, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp; funext reg; by_cases h : reg = .x6 <;> simp [h]
  have step2 : ordinaryStep s₂ (.base (.ADDI .x6 .x6 784)) = some s₃ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₂, s₃, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp; funext reg; by_cases h : reg = .x6 <;> simp [h]
  have step3 : ordinaryStep s₃ (.base (.MUL .x11 .x16 .x6)) = some s₄ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₃, s₄, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step4 : ordinaryStep s₄ (.base (.ADDI .x5 .x0 1)) = some s₅ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₄, s₅, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step5 : ordinaryStep s₅ (.base (.ADDI .x10 .x0 0)) = some s₆ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₅, s₆, openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  rw [Nat.add_comm 7 fuel]
  simp only [execute, fetch0, step0, fetch1, step1, fetch2, step2, fetch3, step3,
    fetch4, step4, fetch5, step5, fetch6, instructionCycles, bind_assoc, pure_bind]
  dsimp only [s₆, openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [Execution.charge]

/-- Reporting the normal proof length cannot overflow a 64-bit register. -/
theorem opening_exit_length (state : MachineState) (positions : Nat)
    (bounded : positions ≤ LENGTH)
    (count : state.getReg .x16 = BitVec.ofNat 64 positions) :
    ((openingExitState state).getReg .x11).toNat = 784 * positions := by
  dsimp only [openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  change ((state.getReg .x16) * (784 : BitVec 64)).toNat = 784 * positions
  rw [count]
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  norm_num [LENGTH, LOG_LENGTH] at bounded
  rw [Nat.mod_eq_of_lt (by omega : positions < 2^64)]
  change (positions * 784) % 18446744073709551616 = 784 * positions
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Final machine state for cap-table exit (`k = 128`), reporting `75776` proof bytes. -/
private def openingCapExitInstructions : List Instr :=
  [.ADDI .x11 .x0 0, .SLLI .x11 .x11 11, .ADDI .x11 .x11 37,
   .SLLI .x11 .x11 11, .ADDI .x11 .x11 0, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0]

private def openingCapExitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCapExitInstructions.take count).foldl execInstrBr state

def openingCapExitState (state : MachineState) : MachineState :=
  openingCapExitPrefix state 7

theorem opening_cap_exit_memory (state : MachineState) :
    (openingCapExitState state).mem = state.mem := rfl

theorem opening_cap_exit_length (state : MachineState) :
    ((openingCapExitState state).getReg .x11).toNat = 75776 := by
  simp [openingCapExitState, openingCapExitPrefix, openingCapExitInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- Cap-table return block (4424): 7 ordinary instructions plus HALT = 8 cycles. -/
theorem opening_cap_exit (state : MachineState) (pc : state.pc = 4424)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (8 + fuel) state allowCoins =
      pure ⟨.success, openingCapExitState state, 8, 0⟩ := by
  have prefixRun (remaining : Nat) :
      execute (submission.image .opening) (7 + remaining) state allowCoins =
        (do let result ← execute (submission.image .opening) remaining
              (openingCapExitState state) allowCoins
            return result.charge 7 0) := by
    apply execute_unit_steps (states := openingCapExitPrefix state)
    intro i hi
    refine ⟨.base ((openingCapExitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply opening_fetch _ (82 + i) _ (by omega)
      · interval_cases i <;>
          simp [openingCapExitPrefix, openingCapExitInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have exitPC : (openingCapExitState state).pc = 4452 := by
    simp [openingCapExitState, openingCapExitPrefix, openingCapExitInstructions, execInstrBr, pc,
      MachineState.setPC]
  have f7 : fetch (submission.image .opening) (openingCapExitState state) = some (.base .ECALL) := by
    apply opening_fetch _ 89 _ (by decide) exitPC; rfl
  have r5 : (openingCapExitState state).getReg .x5 = 1 := by
    dsimp only [openingCapExitState, openingCapExitPrefix, openingCapExitInstructions,
      List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    simp
  have r10 : (openingCapExitState state).getReg .x10 = 0 := by
    dsimp only [openingCapExitState, openingCapExitPrefix, openingCapExitInstructions,
      List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    simp
  rw [show 8 + fuel = 7 + (fuel + 1) by omega, prefixRun]
  simp only [execute, f7, r5, r10, bind_assoc, pure_bind]
  simp [Execution.charge]

/-- All three digest copies in the opening image use these four aligned loads and stores. -/
private def openingCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16,
   .LD .x6 .x23 24, .SD .x25 .x6 24]

private def openingCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCopyInstructions.take count).foldl execInstrBr state

def openingCopyState (state : MachineState) : MachineState :=
  openingCopyPrefix state 8

theorem opening_copy_expansion (state : MachineState) :
    openingCopyState state =
      ([.LD .x6 .x23 0, .SD .x25 .x6 0,
        .LD .x6 .x23 8, .SD .x25 .x6 8,
        .LD .x6 .x23 16, .SD .x25 .x6 16,
        .LD .x6 .x23 24, .SD .x25 .x6 24] : List Instr).foldl execInstrBr state := rfl

private theorem copy_getReg_setMem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem copy_getMem_setMem (state : MachineState) (address value query : Word) :
    (state.setMem address value).getMem query =
      if query = address then value else state.getMem query := by
  simp [MachineState.getMem, MachineState.setMem]

private theorem opening_copy_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingCopyPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [openingCopyPrefix, openingCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, copy_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem opening_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingCopyState state).getReg reg = state.getReg reg :=
  opening_copy_prefix_register state 8 (by decide) reg scratch

set_option maxHeartbeats 1200000 in
/-- All three 32-byte digest copies (sibling, cap left, cap right) take eight cycles. -/
theorem opening_copy (state : MachineState) (start : Nat)
    (location : start = 39 ∨ start = 60 ∨ start = 70)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := openingCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp [openingCopyPrefix, openingCopyInstructions, execInstrBr, pc,
          MachineState.setPC]
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have sourceReg := opening_copy_prefix_register state i (by omega) .x23 (by decide)
    have destinationReg := opening_copy_prefix_register state i (by omega) .x25 (by decide)
    have valid : memoryArgumentsValid (openingCopyPrefix state i)
        ((openingCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [openingCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem opening_digest_access_valid (address : Word)
    (bounded : address.toNat + 32 ≤ MEMORY_BYTES)
    (aligned : address.toNat % 8 = 0) (word : Fin 4) :
    accessValid (address + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have small : 8 * word.val < 2 ^ 64 := by omega
  have total : address.toNat + 8 * word.val < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have value : (address + BitVec.ofNat 64 (8 * word.val)).toNat =
      address.toNat + 8 * word.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  simp only [accessValid, rangeValid, value, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

theorem opening_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 4,
      address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) :
    (openingCopyState state).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have h3 := outside ⟨3, by decide⟩
  have a0 : address ≠ state.getReg .x25 := by simpa using h0
  have a1 : address ≠ state.getReg .x25 + 8#64 := h1
  have a2 : address ≠ state.getReg .x25 + 16#64 := h2
  have a3 : address ≠ state.getReg .x25 + 24#64 := h3
  simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    copy_getReg_setMem, copy_getMem_setMem, signExtend12, a0, a1, a2, a3]

theorem opening_copy_memory (state : MachineState)
    (separated : ∀ source destination : Fin 4,
      state.getReg .x23 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x25 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 4) :
    (openingCopyState state).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  have h10 : state.getReg .x23 + 8#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 + 8#64 :=
    separated ⟨2, by decide⟩ ⟨1, by decide⟩
  have h30 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨3, by decide⟩ ⟨0, by decide⟩
  have h31 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 + 8#64 :=
    separated ⟨3, by decide⟩ ⟨1, by decide⟩
  have h32 : state.getReg .x23 + 24#64 ≠ state.getReg .x25 + 16#64 :=
    separated ⟨3, by decide⟩ ⟨2, by decide⟩
  fin_cases word <;>
    simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      copy_getReg_setMem, signExtend12,
      h10, h20, h21, h30, h31, h32]

theorem opening_copy_pc (state : MachineState) :
    (openingCopyState state).pc = state.pc + 32 := by
  simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

/-- Two-word copy for one 16-byte salt (indices 27..30, PC 4204..4216). -/
private def openingSaltCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8]

private def openingSaltCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSaltCopyInstructions.take count).foldl execInstrBr state

def openingSaltCopyState (state : MachineState) : MachineState :=
  openingSaltCopyPrefix state 4

private theorem opening_salt_copy_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 4) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingSaltCopyPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [openingSaltCopyPrefix, openingSaltCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, copy_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem opening_salt_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingSaltCopyState state).getReg reg = state.getReg reg :=
  opening_salt_copy_prefix_register state 4 (by decide) reg scratch

theorem opening_salt_copy_pc (state : MachineState) :
    (openingSaltCopyState state).pc = state.pc + 16 := by
  simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem opening_salt_copy (state : MachineState) (pc : state.pc = 4204)
    (sourceValid : ∀ word : Fin 2,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltCopyState state) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := openingSaltCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (27 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingSaltCopyPrefix, openingSaltCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have sourceReg := opening_salt_copy_prefix_register state i (by omega) .x23 (by decide)
    have destinationReg := opening_salt_copy_prefix_register state i (by omega) .x25 (by decide)
    have valid : memoryArgumentsValid (openingSaltCopyPrefix state i)
        ((openingSaltCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact d0 | exact d1
    interval_cases i <;>
      simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem opening_salt_access_valid (address : Word)
    (bounded : address.toNat + 16 ≤ MEMORY_BYTES)
    (aligned : address.toNat % 8 = 0) (word : Fin 2) :
    accessValid (address + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have small : 8 * word.val < 2 ^ 64 := by omega
  have total : address.toNat + 8 * word.val < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have value : (address + BitVec.ofNat 64 (8 * word.val)).toNat =
      address.toNat + 8 * word.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt total]
  simp only [accessValid, rangeValid, value, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

theorem opening_salt_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 2,
      address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) :
    (openingSaltCopyState state).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have a0 : address ≠ state.getReg .x25 := by simpa using h0
  have a1 : address ≠ state.getReg .x25 + 8#64 := h1
  simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    copy_getReg_setMem, copy_getMem_setMem, signExtend12, a0, a1]

theorem opening_salt_copy_memory (state : MachineState)
    (separated : ∀ source destination : Fin 2,
      state.getReg .x23 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x25 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 2) :
    (openingSaltCopyState state).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  have h10 : state.getReg .x23 + 8#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨1, by decide⟩ ⟨0, by decide⟩
  fin_cases word <;>
    simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      copy_getReg_setMem, signExtend12, h10]

theorem opening_salt_copy_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 16 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingSaltCopyState state).getMem address = state.getMem address := by
  apply opening_salt_copy_memory_outside
  intro word equal
  have small : (state.getReg .x25).toNat + 8 * word.val < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have same := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * word.val < 2 ^ 64), Nat.mod_eq_of_lt small] at same
  omega

private def openingPathInstructions : List Instr :=
  [.XORI .x7 .x20 1, .SRLI .x6 .x20 1, .ADD .x7 .x7 .x6, .SLLI .x7 .x7 5, .ADD .x23 .x9 .x7]

private def openingPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPathInstructions.take count).foldl execInstrBr state

/-- Compute the sibling's gap-heap address: `t = s xor 1`, then `32*(t + s/2)`. -/
def openingPathPreparedState (state : MachineState) : MachineState :=
  openingPathPrefix state 5

private theorem opening_path_prepare (state : MachineState) (pc : state.pc = 4232)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathPreparedState state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingPathPrefix state)
  intro i hi
  refine ⟨.base ((openingPathInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (34 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPathPrefix, openingPathInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem opening_path_prepare_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x7) (source : reg ≠ .x23) (half : reg ≠ .x6) :
    (openingPathPreparedState state).getReg reg = state.getReg reg := by
  dsimp only [openingPathPreparedState, openingPathPrefix, openingPathInstructions,
    List.take, List.foldl, execInstrBr]
  simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm half),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source)]

theorem opening_path_source (state : MachineState) :
    (openingPathPreparedState state).getReg .x23 =
      state.getReg .x9 + (((state.getReg .x20 ^^^ 1) + (state.getReg .x20 >>> 1)) <<< 5) := by
  simp [openingPathPreparedState, openingPathPrefix, openingPathInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, signExtend12]

/-- Advance the output pointer and move from the current tree node to its parent. -/
def openingPathAdvancedState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x20
    (state.getReg .x20 >>> 1)).setPC 4292

private theorem opening_path_advance (state : MachineState) (pc : state.pc = 4284)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathAdvancedState state) allowCoins
          return result.charge 2 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x25 .x25 32)) := by
    apply opening_fetch state 47 _ (by decide) pc; rfl
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4288
  have second : fetch (submission.image .opening) next =
      some (.base (.SRLI .x20 .x20 1)) := by
    apply opening_fetch next 48 _ (by decide) rfl; rfl
  have step : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have shift : ordinaryStep next (.base (.SRLI .x20 .x20 1)) =
      some (openingPathAdvancedState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      next, openingPathAdvancedState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [show 2 + fuel = (fuel + 1) + 1 by omega]
  rw [execute_ordinary_step _ _ _ _ _ _ first step,
    execute_ordinary_step _ _ _ _ _ _ second shift]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- A full sibling iteration: compute its address, copy 32 bytes, advance the
pointers, and decrement/branch on the remaining path length. -/
def openingPathState (state : MachineState) : MachineState :=
  openingLatchState (openingPathAdvancedState
    (openingCopyState (openingPathPreparedState state)))

/-- Exact seventeen-cycle iteration of the submitted opening program. -/
theorem opening_path_iteration (state : MachineState) (pc : state.pc = 4232)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + (((state.getReg .x20 ^^^ 1) + (state.getReg .x20 >>> 1)) <<< 5) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (17 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState state) allowCoins
          return result.charge 17 0) := by
  let ready := openingPathPreparedState state
  let copied := openingCopyState ready
  have readyPC : ready.pc = 4252 := by
    simp [ready, openingPathPreparedState, openingPathPrefix, openingPathInstructions,
      execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4284 := by rw [opening_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 4,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_source]
    exact sourceValid word
  have writes : ∀ word : Fin 4,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_prepare_register state .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 17 + fuel = 5 + (8 + (2 + (2 + fuel))) by omega,
    opening_path_prepare state pc,
    opening_copy ready 39 (Or.inl rfl) readyPC reads writes,
    opening_path_advance copied copiedPC,
    opening_latch (openingPathAdvancedState copied) rfl]
  simp [openingPathState, ready, copied, Execution.charge, ← Nat.add_assoc]

theorem opening_path_registers (state : MachineState) :
    (openingPathState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (openingPathState state).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (openingPathState state).getReg .x28 = state.getReg .x28 - 1 ∧
    (openingPathState state).getReg .x16 = state.getReg .x16 ∧
    (openingPathState state).getReg .x9 = state.getReg .x9 := by
  simp [openingPathState, openingLatchState, openingPathAdvancedState,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    opening_copy_register, opening_path_prepare_register]

theorem opening_sibling_offset (node : Word) (nodeBound : node.toNat < 2 ^ 25) :
    (((node ^^^ 1) + (node >>> 1)) <<< 5).toNat = heapOffset (node.toNat ^^^ 1) := by
  have siblingBound : node.toNat ^^^ 1 < 2 ^ 25 :=
    Nat.xor_lt_two_pow nodeBound (by decide)
  have half : (node >>> 1).toNat = node.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, pow_one]
  have sum : ((node ^^^ 1) + (node >>> 1)).toNat = (node.toNat ^^^ 1) + node.toNat / 2 := by
    simp only [BitVec.toNat_add, half, BitVec.toNat_xor]
    change ((node.toNat ^^^ 1) + node.toNat / 2) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    omega
  rw [heap_offset_sibling]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, sum]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem opening_sibling_access (heap node : Word)
    (heapBound : heap.toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : heap.toNat % 8 = 0) (nodeBound : node.toNat < 2 ^ 25)
    (word : Fin 4) :
    accessValid (heap + (((node ^^^ 1) + (node >>> 1)) <<< 5) +
      BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have siblingBound : node.toNat ^^^ 1 < 2 ^ 25 :=
    Nat.xor_lt_two_pow nodeBound (by decide)
  have offset := opening_sibling_offset node nodeBound
  have inside := heap_offset_bound (node.toNat ^^^ 1) (2^24) (by omega)
  have aligned := heap_offset_aligned (node.toNat ^^^ 1)
  have total : heap.toNat + heapOffset (node.toNat ^^^ 1) < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at heapBound
    omega
  have address : (heap + (((node ^^^ 1) + (node >>> 1)) <<< 5)).toNat =
      heap.toNat + heapOffset (node.toNat ^^^ 1) := by
    simp only [BitVec.toNat_add, offset, Nat.mod_eq_of_lt total]
  apply opening_digest_access_valid
  · rw [address]
    simp only [MEMORY_BYTES] at heapBound ⊢
    omega
  · rw [address]
    omega

private theorem copy_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

private theorem opening_path_pc (state : MachineState) :
    (openingPathState state).pc =
      if state.getReg .x28 - 1 = 0 then 4300 else 4232 := by
  simp [openingPathState, openingLatchState, openingPathAdvancedState,
    copy_pc_setPC, MachineState.getReg_setReg_ne,
    opening_copy_register, opening_path_prepare_register]

theorem opening_path_loop (remaining : Nat) (bounded : remaining ≤ LOG_LENGTH)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4232)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (nodeBound : (state.getReg .x20).toNat < 2 ^ 25)
    (outputBound : (state.getReg .x25).toNat + 32 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (17 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState^[remaining] state) allowCoins
          return result.charge (17 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      simp only [LOG_LENGTH] at bounded; omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPathState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_path_registers state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPathState state).pc = 4232 := by
      intro positive
      rw [opening_path_pc, counter, subtract, if_neg]
      intro zero
      have := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt small] at this
      omega
    have nextHeap : (openingPathState state).getReg .x9 = state.getReg .x9 :=
      (opening_path_registers state).2.2.2.2
    have nextNode : ((openingPathState state).getReg .x20).toNat < 2 ^ 25 := by
      rw [(opening_path_registers state).2.1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    have outputNat : ((openingPathState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 32 := by
      rw [(opening_path_registers state).1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat + 32) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at outputBound
      omega
    have nextOutputBound : ((openingPathState state).getReg .x25).toNat +
        32 * remaining ≤ MEMORY_BYTES := by rw [outputNat]; omega
    have nextOutputAligned : ((openingPathState state).getReg .x25).toNat % 8 = 0 := by
      rw [outputNat]; omega
    have reads := opening_sibling_access (state.getReg .x9) (state.getReg .x20)
      heapBound heapAligned nodeBound
    have writes := opening_digest_access_valid (state.getReg .x25) (by omega) outputAligned
    rw [show 17 * (remaining + 1) + fuel = 17 + (17 * remaining + fuel) by omega,
      opening_path_iteration state (pc (by omega)) reads writes,
      ih (by omega) (openingPathState state) nextCounter nextPC
        (by simpa only [nextHeap] using heapBound)
        (by simpa only [nextHeap] using heapAligned)
        nextNode nextOutputBound nextOutputAligned]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm]

theorem opening_path_finished (remaining : Nat) (positive : 0 < remaining)
    (bounded : remaining ≤ LOG_LENGTH) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (openingPathState^[remaining] state).pc = 4300 ∧
    (openingPathState^[remaining] state).getReg .x28 = 0 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPathState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_path_registers state).2.2.1, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      constructor
      · rw [opening_path_pc, counter, subtract]; rfl
      · exact nextCounter
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (by omega) (openingPathState state) nextCounter

private theorem opening_path_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (sibling : reg ≠ .x7) (index : reg ≠ .x20)
    (source : reg ≠ .x23) (output : reg ≠ .x25) (counter : reg ≠ .x28) :
    (openingPathState state).getReg reg = state.getReg reg := by
  simp only [openingPathState, openingLatchState, openingPathAdvancedState,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm counter),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm index),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm output)]
  rw [opening_copy_register _ reg scratch,
    opening_path_prepare_register _ reg sibling source scratch]

private theorem opening_path_preserves_register (iterations : Nat) (state : MachineState)
    (reg : Reg) (scratch : reg ≠ .x6) (sibling : reg ≠ .x7) (index : reg ≠ .x20)
    (source : reg ≠ .x23) (output : reg ≠ .x25) (counter : reg ≠ .x28) :
    (openingPathState^[iterations] state).getReg reg = state.getReg reg := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply',
      opening_path_register _ reg scratch sibling index source output counter, ih]

theorem opening_path_output (iterations : Nat) (state : MachineState) :
    (openingPathState^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (32 * iterations) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_path_registers _).1, ih]
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

private def openingPositionInstructions : List Instr :=
  [.LD .x20 .x24 0, .SLLI .x6 .x20 4, .ADD .x23 .x18 .x6]

private def openingPositionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPositionInstructions.take count).foldl execInstrBr state

/-- Read the next serialized position and compute its 16-byte salt address. -/
def openingPositionPreparedState (state : MachineState) : MachineState :=
  openingPositionPrefix state 3

private theorem opening_position_prepare (state : MachineState) (pc : state.pc = 4192)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPreparedState state) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := openingPositionPrefix state)
  intro i hi
  refine ⟨.base ((openingPositionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (24 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPositionPrefix, openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i
    · simpa [openingPositionPrefix, openingPositionInstructions, ordinaryStep,
        memoryArgumentsValid, memAccess, signExtend12] using indexValid
    · rfl
    · rfl
  · interval_cases i <;> rfl

theorem opening_position_prepare_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (index : reg ≠ .x20) (source : reg ≠ .x23) :
    (openingPositionPreparedState state).getReg reg = state.getReg reg := by
  dsimp only [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
    List.take, List.foldl, execInstrBr]
  simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm index),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source)]

theorem opening_position_prepared (state : MachineState) :
    (openingPositionPreparedState state).getReg .x20 = state.getMem (state.getReg .x24) ∧
    (openingPositionPreparedState state).getReg .x23 =
      state.getReg .x18 + (state.getMem (state.getReg .x24) <<< 4) := by
  simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, signExtend12]

private def openingSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 16, .ADD .x20 .x20 .x19, .ADDI .x28 .x30 0]

private def openingSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSaltInstructions.take count).foldl execInstrBr state

/-- After the 16-byte salt copy, advance the proof pointer by 16, enter the leaf's heap slot,
and copy the active path depth from `x30` into `x28`. -/
def openingSaltAdvancedState (state : MachineState) : MachineState :=
  openingSaltPrefix state 3

private theorem opening_salt_advance (state : MachineState) (pc : state.pc = 4220)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltAdvancedState state) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := openingSaltPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (31 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingSaltPrefix, openingSaltInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem opening_salt_register (state : MachineState) (reg : Reg)
    (output : reg ≠ .x25) (index : reg ≠ .x20) (counter : reg ≠ .x28) :
    (openingSaltAdvancedState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [openingSaltAdvancedState, openingSaltPrefix,
    openingSaltInstructions, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, signExtend12]

private theorem opening_salt_advanced (state : MachineState) :
    (openingSaltAdvancedState state).getReg .x25 = state.getReg .x25 + 16 ∧
    (openingSaltAdvancedState state).getReg .x20 = state.getReg .x20 + state.getReg .x19 ∧
    (openingSaltAdvancedState state).getReg .x28 = state.getReg .x30 ∧
    (openingSaltAdvancedState state).pc = state.pc + 12 := by
  simp [openingSaltAdvancedState, openingSaltPrefix, openingSaltInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    signExtend12, BitVec.add_assoc]

/-- State at the sibling-loop entry (4232) after copying this position's 16-byte salt. -/
def openingPositionPathState (state : MachineState) : MachineState :=
  openingSaltAdvancedState (openingSaltCopyState (openingPositionPreparedState state))

/-- Position setup and 16-byte salt copy take ten cycles. -/
theorem opening_position_setup (state : MachineState) (pc : state.pc = 4192)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (sourceValid : ∀ word : Fin 2,
      accessValid (state.getReg .x18 + (state.getMem (state.getReg .x24) <<< 4) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (10 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPathState state) allowCoins
          return result.charge 10 0) := by
  let ready := openingPositionPreparedState state
  let copied := openingSaltCopyState ready
  have readyPC : ready.pc = 4204 := by
    simp [ready, openingPositionPreparedState, openingPositionPrefix,
      openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4220 := by rw [opening_salt_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 2,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [(opening_position_prepared state).2]
    exact sourceValid word
  have writes : ∀ word : Fin 2,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 10 + fuel = 3 + (4 + (3 + fuel)) by omega,
    opening_position_prepare state pc indexValid,
    opening_salt_copy ready readyPC reads writes,
    opening_salt_advance copied copiedPC]
  simp [openingPositionPathState, ready, copied, Execution.charge, ← Nat.add_assoc]

theorem opening_position_path_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (index : reg ≠ .x20) (source : reg ≠ .x23)
    (output : reg ≠ .x25) (counter : reg ≠ .x28) :
    (openingPositionPathState state).getReg reg = state.getReg reg := by
  rw [openingPositionPathState, opening_salt_register _ reg output index counter,
    opening_salt_copy_register _ reg scratch,
    opening_position_prepare_register _ reg scratch index source]

theorem opening_position_path_registers (state : MachineState) :
    (openingPositionPathState state).getReg .x25 = state.getReg .x25 + 16 ∧
    (openingPositionPathState state).getReg .x20 =
      state.getMem (state.getReg .x24) + state.getReg .x19 ∧
    (openingPositionPathState state).getReg .x28 = state.getReg .x30 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [openingPositionPathState, (opening_salt_advanced _).1,
      opening_salt_copy_register _ .x25 (by decide),
      opening_position_prepare_register _ .x25 (by decide) (by decide) (by decide)]
  · rw [openingPositionPathState, (opening_salt_advanced _).2.1,
      opening_salt_copy_register _ .x20 (by decide), opening_salt_copy_register _ .x19 (by decide),
      (opening_position_prepared state).1,
      opening_position_prepare_register _ .x19 (by decide) (by decide) (by decide)]
  · rw [openingPositionPathState, (opening_salt_advanced _).2.2.1,
      opening_salt_copy_register _ .x30 (by decide),
      opening_position_prepare_register _ .x30 (by decide) (by decide) (by decide)]

/-- 16-byte salt lookup is safe for every valid vector index. -/
theorem opening_salt_access (salts index : Word)
    (saltBound : salts.toNat + 2 ^ 28 ≤ MEMORY_BYTES)
    (saltAligned : salts.toNat % 8 = 0) (indexBound : index.toNat < 2 ^ 24)
    (word : Fin 2) :
    accessValid (salts + (index <<< 4) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have offset : (index <<< 4).toNat = index.toNat * 16 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (index.toNat * 16) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt]
    omega
  have total : salts.toNat + index.toNat * 16 < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at saltBound
    omega
  have address : (salts + (index <<< 4)).toNat = salts.toNat + index.toNat * 16 := by
    simp only [BitVec.toNat_add, offset, Nat.mod_eq_of_lt total]
  apply opening_salt_access_valid
  · rw [address]; omega
  · rw [address]; omega

/-- State after one complete 16-byte salt-plus-path opening of `pathDepth` siblings. -/
def openingPositionState (pathDepth : Nat) (state : MachineState) : MachineState :=
  openingNextState (openingPathState^[pathDepth] (openingPositionPathState state))

/-- One complete position with `pathDepth` siblings costs `13 + 17 * pathDepth` cycles
(`421` for depth 24, `302` for depth 17) and makes no queries. -/
theorem opening_position (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ LOG_LENGTH) (state : MachineState)
    (pc : state.pc = 4192)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 28 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + (16 + 32 * pathDepth) ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (13 + 17 * pathDepth + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState pathDepth state) allowCoins
          return result.charge (13 + 17 * pathDepth) 0) := by
  let path := openingPositionPathState state
  have pathPC : path.pc = 4232 := by
    change (openingPositionPathState state).pc = 4232
    rw [openingPositionPathState, (opening_salt_advanced _).2.2.2, opening_salt_copy_pc]
    simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
      execInstrBr, pc, MachineState.setPC]
  have pathCounter : path.getReg .x28 = BitVec.ofNat 64 pathDepth :=
    (opening_position_path_registers state).2.2.trans depthReg
  have pathHeap : path.getReg .x9 = state.getReg .x9 :=
    opening_position_path_register state .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat < 2 ^ 25 := by
    rw [(opening_position_path_registers state).2.1, leaves, BitVec.toNat_add]
    change ((state.getMem (state.getReg .x24)).toNat + 16777216) % 2 ^ 64 < 2 ^ 25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 16 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 16) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat + 32 * pathDepth ≤ MEMORY_BYTES := by
    rw [outputNat]; omega
  have pathAligned : (path.getReg .x25).toNat % 8 = 0 := by rw [outputNat]; omega
  have finishedPC : (openingPathState^[pathDepth] path).pc = 4300 :=
    (opening_path_finished pathDepth depthPos depthBound path pathCounter).1
  have reads := opening_salt_access (state.getReg .x18) (state.getMem (state.getReg .x24))
    saltBound saltAligned indexBound
  have writes := opening_salt_access_valid (state.getReg .x25) (by omega) outputAligned
  rw [show 13 + 17 * pathDepth + fuel = 10 + (17 * pathDepth + (3 + fuel)) by omega,
    opening_position_setup state pc indexValid reads writes,
    opening_path_loop pathDepth depthBound path pathCounter (fun _ => pathPC)
      (by simpa only [pathHeap] using heapBound)
      (by simpa only [pathHeap] using heapAligned) pathNode pathOutput pathAligned,
    opening_next _ finishedPC]
  simp only [openingPositionState, path, bind_assoc, pure_bind]
  apply bind_congr
  intro res
  congr 1
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  constructor <;> omega

/-- One position advances the input by 8 bytes and proof output by `16 + 32 * pathDepth` bytes,
while preserving `x16` and `x30`. -/
theorem opening_position_progress (pathDepth : Nat) (state : MachineState) :
    (openingPositionState pathDepth state).getReg .x24 = state.getReg .x24 + 8 ∧
    (openingPositionState pathDepth state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (16 + 32 * pathDepth) ∧
    (openingPositionState pathDepth state).getReg .x27 = state.getReg .x27 - 1 ∧
    (openingPositionState pathDepth state).getReg .x16 = state.getReg .x16 ∧
    (openingPositionState pathDepth state).getReg .x30 = state.getReg .x30 := by
  have outPtr : (openingPositionState pathDepth state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (16 + 32 * pathDepth) := by
    simp only [openingPositionState, openingNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ .x25),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x24 ≠ .x25),
      opening_path_output, (opening_position_path_registers state).1]
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  refine ⟨?_, outPtr, ?_, ?_, ?_⟩ <;>
    simp [-Function.iterate_succ, openingPositionState, openingNextState,
      MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      opening_path_preserves_register, opening_position_path_register]

theorem opening_position_bases (pathDepth : Nat) (state : MachineState) :
    (openingPositionState pathDepth state).getReg .x9 = state.getReg .x9 ∧
    (openingPositionState pathDepth state).getReg .x18 = state.getReg .x18 ∧
    (openingPositionState pathDepth state).getReg .x19 = state.getReg .x19 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState,
    MachineState.getReg_setReg_ne, opening_path_preserves_register,
    opening_position_path_register]

private theorem opening_position_pc (pathDepth : Nat) (state : MachineState) :
    (openingPositionState pathDepth state).pc =
      if state.getReg .x27 - 1 = 0 then 4312 else 4192 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState, copy_pc_setPC,
    opening_path_preserves_register, opening_position_path_register]

theorem opening_copy_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 32 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingCopyState state).getMem address = state.getMem address := by
  apply opening_copy_memory_outside
  intro word equal
  have small : (state.getReg .x25).toNat + 8 * word.val < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have same := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * word.val < 2 ^ 64), Nat.mod_eq_of_lt small] at same
  omega

private theorem opening_path_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 32 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPathState state).getMem address = state.getMem address := by
  simp only [openingPathState, openingLatchState, openingPathAdvancedState,
    MachineState.getMem_setPC, MachineState.getMem_setReg]
  rw [opening_copy_memory_below]
  · simp [openingPathPreparedState, openingPathPrefix, openingPathInstructions, execInstrBr]
  · simpa only [opening_path_prepare_register state .x25 (by decide) (by decide) (by decide)] using bounded
  · simpa only [opening_path_prepare_register state .x25 (by decide) (by decide) (by decide)] using below

theorem opening_path_loop_memory_below (iterations : Nat) (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 32 * iterations ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPathState^[iterations] state).getMem address = state.getMem address := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    have outputNat : ((openingPathState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 32 := by
      rw [(opening_path_registers state).1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat + 32) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at bounded
      omega
    rw [Function.iterate_succ_apply, ih]
    · exact opening_path_memory_below state address (by omega) below
    · rw [outputNat]; omega
    · rw [outputNat]; omega

/-- A complete salt-and-path opening preserves all memory before its proof output. -/
theorem opening_position_memory_below (pathDepth : Nat) (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + (16 + 32 * pathDepth) ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPositionState pathDepth state).getMem address = state.getMem address := by
  let path := openingPositionPathState state
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 16 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 16) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at bounded
    omega
  have saltMemory : path.getMem address = state.getMem address := by
    change (openingSaltAdvancedState (openingSaltCopyState
      (openingPositionPreparedState state))).getMem address = _
    have advanceMemory (initial : MachineState) :
        (openingSaltAdvancedState initial).getMem address = initial.getMem address := by
      simp [openingSaltAdvancedState, openingSaltPrefix, openingSaltInstructions,
        execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
        MachineState.getMem, signExtend12]
    rw [advanceMemory, opening_salt_copy_memory_below]
    · simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions, execInstrBr]
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)]
        using (show (state.getReg .x25).toNat + 16 ≤ MEMORY_BYTES by omega)
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)] using below
  simp only [openingPositionState, openingNextState, MachineState.getMem_setPC, MachineState.getMem_setReg]
  rw [opening_path_loop_memory_below pathDepth path address, saltMemory]
  · rw [outputNat]; omega
  · rw [outputNat]; omega

private theorem opening_address_add (address : Word) (offset : Nat)
    (bounded : address.toNat + offset ≤ MEMORY_BYTES) :
    (address + BitVec.ofNat 64 offset).toNat = address.toNat + offset := by
  have small : address.toNat + offset < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2 ^ 64), Nat.mod_eq_of_lt small]

set_option maxRecDepth 4096 in
/-- Execute all remaining positions at depth `pathDepth` (`24` or `17`). -/
theorem opening_positions_loop (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ LOG_LENGTH)
    (remaining : Nat) (bounded : remaining ≤ LENGTH)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (pc : 0 < remaining → state.pc = 4192)
    (indices : ∀ offset < remaining,
      (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24)
    (indexSpace : (state.getReg .x24).toNat + 8 * remaining ≤ (state.getReg .x25).toNat)
    (indexAligned : (state.getReg .x24).toNat % 8 = 0)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 28 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + (16 + 32 * pathDepth) * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) ((13 + 17 * pathDepth) * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            ((openingPositionState pathDepth)^[remaining] state) allowCoins
          return result.charge ((13 + 17 * pathDepth) * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      norm_num [LENGTH, LOG_LENGTH] at bounded; omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have prog := opening_position_progress pathDepth state
    have nextCounter : (openingPositionState pathDepth state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [prog.2.2.1, counter, subtract]
    have nextDepth : (openingPositionState pathDepth state).getReg .x30 = BitVec.ofNat 64 pathDepth :=
      prog.2.2.2.2.trans depthReg
    have nextPC : 0 < remaining → (openingPositionState pathDepth state).pc = 4192 := by
      intro positive
      rw [opening_position_pc, counter, subtract, if_neg]
      intro zero
      have equal := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at equal
      rw [Nat.mod_eq_of_lt small] at equal
      omega
    have nextIndex : ((openingPositionState pathDepth state).getReg .x24).toNat =
        (state.getReg .x24).toNat + 8 := by
      rw [prog.1]
      exact opening_address_add (state.getReg .x24) 8 (by omega)
    have recordLe : (state.getReg .x25).toNat + (16 + 32 * pathDepth) ≤ MEMORY_BYTES := by
      have : (16 + 32 * pathDepth) * 1 ≤ (16 + 32 * pathDepth) * (remaining + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have nextOutput : ((openingPositionState pathDepth state).getReg .x25).toNat =
        (state.getReg .x25).toNat + (16 + 32 * pathDepth) := by
      rw [prog.2.1]
      exact opening_address_add (state.getReg .x25) (16 + 32 * pathDepth) recordLe
    have nextIndices : ∀ offset < remaining,
        ((openingPositionState pathDepth state).getMem
          ((openingPositionState pathDepth state).getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset offsetBound
      have address : (openingPositionState pathDepth state).getReg .x24 + BitVec.ofNat 64 (8 * offset) =
          state.getReg .x24 + BitVec.ofNat 64 (8 * (offset + 1)) := by
        rw [prog.1]
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        rw [BitVec.add_comm (8 : Word)]
        rfl
      rw [address, opening_position_memory_below pathDepth]
      · exact indices (offset + 1) (by omega)
      · exact recordLe
      · rw [opening_address_add _ _ (by omega)]
        omega
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, indexAligned⟩
    have indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using indices 0 (by omega)
    have nextBases := opening_position_bases pathDepth state
    have stepSplit : (13 + 17 * pathDepth) * (remaining + 1) + fuel =
        (13 + 17 * pathDepth) + ((13 + 17 * pathDepth) * remaining + fuel) := by
      rw [Nat.mul_succ]; omega
    rw [stepSplit,
      opening_position pathDepth depthPos depthBound state (pc (by omega)) depthReg
        indexValid indexBound leaves saltBound saltAligned heapBound heapAligned
        recordLe outputAligned,
      ih (by omega) (openingPositionState pathDepth state) nextCounter nextDepth nextPC nextIndices
        (by rw [nextIndex, nextOutput]; omega) (by rw [nextIndex]; omega)
        (by simpa only [nextBases.2.2] using leaves)
        (by simpa only [nextBases.2.1] using saltBound)
        (by simpa only [nextBases.2.1] using saltAligned)
        (by simpa only [nextBases.1] using heapBound)
        (by simpa only [nextBases.1] using heapAligned)
        (by rw [nextOutput]; rw [Nat.mul_succ] at outputBound; omega)
        (by rw [nextOutput]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

/-- The complete position loop reaches `open-done` (4312) with its counter at zero. -/
theorem opening_positions_finished (pathDepth remaining : Nat) (positive : 0 < remaining)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    ((openingPositionState pathDepth)^[remaining] state).pc = 4312 ∧
    ((openingPositionState pathDepth)^[remaining] state).getReg .x27 = 0 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPositionState pathDepth state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [(opening_position_progress pathDepth state).2.2.1, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      constructor
      · rw [opening_position_pc, counter, subtract]; rfl
      · exact nextCounter
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (openingPositionState pathDepth state) nextCounter

theorem opening_positions_preserves_count (pathDepth iterations : Nat) (state : MachineState) :
    ((openingPositionState pathDepth)^[iterations] state).getReg .x16 = state.getReg .x16 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_position_progress pathDepth _).2.2.2.1, ih]

theorem opening_positions_preserves_heap (pathDepth iterations : Nat) (state : MachineState) :
    ((openingPositionState pathDepth)^[iterations] state).getReg .x9 = state.getReg .x9 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_position_bases pathDepth _).1, ih]

theorem opening_positions_output (pathDepth iterations : Nat) (state : MachineState) :
    ((openingPositionState pathDepth)^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 ((16 + 32 * pathDepth) * iterations) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_position_progress pathDepth _).2.1, ih]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_succ]

/-! ### Level-7 cap-table copy (`k = 128`) -/

private def openingCapSetupInstructions : List Instr :=
  [.ADDI .x6 .x0 3, .SLLI .x6 .x6 11, .ADD .x23 .x9 .x6, .ADDI .x28 .x0 64]

private def openingCapSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCapSetupInstructions.take count).foldl execInstrBr state

def openingCapSetupState (state : MachineState) : MachineState :=
  openingCapSetupPrefix state 4

theorem opening_cap_setup (state : MachineState) (pc : state.pc = 4320)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapSetupState state) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := openingCapSetupPrefix state)
  intro i hi
  refine ⟨.base ((openingCapSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (56 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingCapSetupPrefix, openingCapSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem opening_cap_setup_registers (state : MachineState) (pc : state.pc = 4320) :
    (openingCapSetupState state).pc = 4336 ∧
    (openingCapSetupState state).getReg .x23 = state.getReg .x9 + 6144 ∧
    (openingCapSetupState state).getReg .x25 = state.getReg .x25 ∧
    (openingCapSetupState state).getReg .x28 = 64 ∧
    (openingCapSetupState state).mem = state.mem := by
  dsimp only [openingCapSetupState, openingCapSetupPrefix, openingCapSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp [pc]

/-- Advance source and destination by 32 bytes between the two halves of a cap pair. -/
def openingCapMidState (state : MachineState) : MachineState :=
  ((state.setReg .x23 (state.getReg .x23 + 32)).setReg .x25 (state.getReg .x25 + 32)).setPC 4376

private theorem opening_cap_mid (state : MachineState) (pc : state.pc = 4368)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapMidState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x23 (state.getReg .x23 + 32)).setPC 4372
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x23 .x23 32)) := by
    apply opening_fetch state 68 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) next = some (.base (.ADDI .x25 .x25 32)) := by
    apply opening_fetch next 69 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x23 .x23 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x25 .x25 32)) = some (openingCapMidState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next,
      openingCapMidState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- After the second digest of a cap pair, skip the 32-byte gap (+64 total on x23),
advance x25 by 32, and decrement x28. -/
def openingCapNextState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x28 - 1
  (((state.setReg .x23 (state.getReg .x23 + 64)).setReg .x25 (state.getReg .x25 + 32)).setReg
    .x28 remaining).setPC (if remaining = 0 then 4424 else 4336)

private theorem opening_cap_next (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapNextState state) allowCoins
          return result.charge 4 0) := by
  let s1 := (state.setReg .x23 (state.getReg .x23 + 64)).setPC 4412
  let s2 := (s1.setReg .x25 (state.getReg .x25 + 32)).setPC 4416
  let s3 := (s2.setReg .x28 (state.getReg .x28 - 1)).setPC 4420
  have f0 : fetch (submission.image .opening) state = some (.base (.ADDI .x23 .x23 64)) := by
    apply opening_fetch state 78 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .opening) s1 = some (.base (.ADDI .x25 .x25 32)) := by
    apply opening_fetch s1 79 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .opening) s2 = some (.base (.ADDI .x28 .x28 4095)) := by
    apply opening_fetch s2 80 _ (by decide) rfl; rfl
  have f3 : fetch (submission.image .opening) s3 = some (.base (.BNE .x28 .x0 8108)) := by
    apply opening_fetch s3 81 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x23 .x23 64)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x25 .x25 32)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have st2 : ordinaryStep s2 (.base (.ADDI .x28 .x28 4095)) = some s3 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2, s3,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st3 : ordinaryStep s3 (.base (.BNE .x28 .x0 8108)) = some (openingCapNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2, s3,
      openingCapNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, f3, st3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One iteration of the cap-table copy loop: copy pair `(2q, 2q+1)` across the gap. -/
def openingCapPairState (state : MachineState) : MachineState :=
  openingCapNextState (openingCopyState (openingCapMidState (openingCopyState state)))

theorem opening_cap_pair_registers (state : MachineState) :
    (openingCapPairState state).getReg .x23 = state.getReg .x23 + 96 ∧
    (openingCapPairState state).getReg .x25 = state.getReg .x25 + 64 ∧
    (openingCapPairState state).getReg .x28 = state.getReg .x28 - 1 := by
  simp [openingCapPairState, openingCapNextState, openingCapMidState,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    opening_copy_register, BitVec.add_assoc]

theorem opening_cap_pair_pc (state : MachineState) :
    (openingCapPairState state).pc =
      if state.getReg .x28 - 1 = 0 then 4424 else 4336 := by
  simp [openingCapPairState, openingCapNextState, openingCapMidState,
    copy_pc_setPC, MachineState.getReg_setReg_ne, opening_copy_register]

theorem opening_cap_pair_iteration (state : MachineState) (pc : state.pc = 4336)
    (srcBound : (state.getReg .x23).toNat + 64 ≤ MEMORY_BYTES)
    (srcAligned : (state.getReg .x23).toNat % 8 = 0)
    (dstBound : (state.getReg .x25).toNat + 64 ≤ MEMORY_BYTES)
    (dstAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (22 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapPairState state) allowCoins
          return result.charge 22 0) := by
  let c1 := openingCopyState state
  let m := openingCapMidState c1
  let c2 := openingCopyState m
  have c1PC : c1.pc = 4368 := by rw [opening_copy_pc, pc]; rfl
  have c2PC : c2.pc = 4408 := by rw [opening_copy_pc]; rfl
  have s1 := opening_digest_access_valid (state.getReg .x23) (by omega) srcAligned
  have d1 := opening_digest_access_valid (state.getReg .x25) (by omega) dstAligned
  have mSrc : m.getReg .x23 = state.getReg .x23 + 32 := by
    simp [m, openingCapMidState, c1, opening_copy_register, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have mDst : m.getReg .x25 = state.getReg .x25 + 32 := by
    simp [m, openingCapMidState, c1, opening_copy_register, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq]
  have mSrcNat : (m.getReg .x23).toNat = (state.getReg .x23).toNat + 32 := by
    rw [mSrc]; exact opening_address_add _ 32 (by omega)
  have mDstNat : (m.getReg .x25).toNat = (state.getReg .x25).toNat + 32 := by
    rw [mDst]; exact opening_address_add _ 32 (by omega)
  have s2 := opening_digest_access_valid (m.getReg .x23) (by rw [mSrcNat]; omega) (by rw [mSrcNat]; omega)
  have d2 := opening_digest_access_valid (m.getReg .x25) (by rw [mDstNat]; omega) (by rw [mDstNat]; omega)
  rw [show 22 + fuel = 8 + (2 + (8 + (4 + fuel))) by omega,
    opening_copy state 60 (Or.inr (Or.inl rfl)) pc s1 d1,
    opening_cap_mid c1 c1PC,
    opening_copy m 70 (Or.inr (Or.inr rfl)) rfl s2 d2,
    opening_cap_next c2 c2PC]
  simp [openingCapPairState, c1, m, c2, Execution.charge, ← Nat.add_assoc]

theorem opening_cap_pair_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 64 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingCapPairState state).getMem address = state.getMem address := by
  let c1 := openingCopyState state
  let m := openingCapMidState c1
  have mDstNat : (m.getReg .x25).toNat = (state.getReg .x25).toNat + 32 := by
    have mDst : m.getReg .x25 = state.getReg .x25 + 32 := by
      simp [m, openingCapMidState, c1, opening_copy_register, MachineState.getReg_setReg_ne,
        MachineState.getReg_setReg_eq]
    rw [mDst]; exact opening_address_add _ 32 (by omega)
  simp only [openingCapPairState, openingCapNextState, MachineState.getMem_setPC, MachineState.getMem_setReg]
  rw [opening_copy_memory_below m address (by rw [mDstNat]; omega) (by rw [mDstNat]; omega)]
  exact opening_copy_memory_below state address (by omega) below

theorem opening_cap_loop_memory_below (iterations : Nat) (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 64 * iterations ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingCapPairState^[iterations] state).getMem address = state.getMem address := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    have nextDst : ((openingCapPairState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 64 := by
      rw [(opening_cap_pair_registers state).2.1]
      exact opening_address_add _ 64 (by omega)
    rw [Function.iterate_succ_apply, ih]
    · exact opening_cap_pair_memory_below state address (by omega) below
    · rw [nextDst]; omega
    · rw [nextDst]; omega

theorem opening_cap_loop (remaining : Nat) (bounded : remaining ≤ 64) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4336)
    (srcBound : (state.getReg .x23).toNat + 96 * remaining ≤ MEMORY_BYTES)
    (srcAligned : (state.getReg .x23).toNat % 8 = 0)
    (dstBound : (state.getReg .x25).toNat + 64 * remaining ≤ MEMORY_BYTES)
    (dstAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (22 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapPairState^[remaining] state) allowCoins
          return result.charge (22 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingCapPairState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_cap_pair_registers state).2.2, counter, subtract]
    have nextPC : 0 < remaining → (openingCapPairState state).pc = 4336 := by
      intro positive
      rw [opening_cap_pair_pc, counter, subtract, if_neg]
      intro zero
      have := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    have nextSrc : ((openingCapPairState state).getReg .x23).toNat =
        (state.getReg .x23).toNat + 96 := by
      rw [(opening_cap_pair_registers state).1]
      exact opening_address_add _ 96 (by omega)
    have nextDst : ((openingCapPairState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 64 := by
      rw [(opening_cap_pair_registers state).2.1]
      exact opening_address_add _ 64 (by omega)
    rw [show 22 * (remaining + 1) + fuel = 22 + (22 * remaining + fuel) by omega,
      opening_cap_pair_iteration state (pc (by omega)) (by omega) srcAligned (by omega) dstAligned,
      ih (by omega) (openingCapPairState state) nextCounter nextPC
        (by rw [nextSrc]; omega) (by rw [nextSrc]; omega)
        (by rw [nextDst]; omega) (by rw [nextDst]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

theorem opening_cap_finished (remaining : Nat) (positive : 0 < remaining)
    (bounded : remaining ≤ 64) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (openingCapPairState^[remaining] state).pc = 4424 ∧
    (openingCapPairState^[remaining] state).getReg .x28 = 0 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingCapPairState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_cap_pair_registers state).2.2, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      constructor
      · rw [opening_cap_pair_pc, counter, subtract]; rfl
      · exact nextCounter
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (by omega) (openingCapPairState state) nextCounter

end CommitGolfCandidate
