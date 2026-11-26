import CommitGolfCandidate.Padding96Call

/-! The checker's dispatch, length gates, root-word comparison, compression call,
and 16-byte tagged-salt leaf subroutine, proved against the submitted image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

theorem check_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 222) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .check).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .check) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .check).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

/-! ### Entry dispatch (`k = 128` vs `k ≠ 128`) -/

private def checkDispatchInstructions : List Instr :=
  [.ADDI .x26 .x11 0, .ADDI .x24 .x13 0, .ADDI .x8 .x14 0,
   .ADDI .x25 .x15 0, .ADDI .x27 .x16 0, .ADDI .x6 .x0 128]

private def checkDispatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkDispatchInstructions.take count).foldl execInstrBr state

private theorem check_dispatch_prefix (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkDispatchPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := checkDispatchPrefix state)
  intro i hi
  refine ⟨.base ((checkDispatchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [checkDispatchPrefix, checkDispatchInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State after initial ABI register copy and dispatch on `x16 = 128` (`4444` for cap
mode, `4124` for normal mode). -/
def checkDispatchState (state : MachineState) : MachineState :=
  (checkDispatchPrefix state 6).setPC (if state.getReg .x16 = 128 then 4444 else 4124)

theorem check_dispatch (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (7 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkDispatchState state) allowCoins
          return result.charge 7 0) := by
  let ready := checkDispatchPrefix state 6
  have readyPC : ready.pc = 4120 := by
    simp [ready, checkDispatchPrefix, checkDispatchInstructions, execInstrBr, pc, MachineState.setPC]
  have ready27 : ready.getReg .x27 = state.getReg .x16 := by
    simp [ready, checkDispatchPrefix, checkDispatchInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have ready6 : ready.getReg .x6 = 128 := by
    dsimp only [ready, checkDispatchPrefix, checkDispatchInstructions, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have fetched : fetch (submission.image .check) ready = some (.base (.BEQ .x27 .x6 324)) := by
    apply check_fetch ready 6 _ (by decide) readyPC; rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x6 324)) = some (checkDispatchState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [ready27, ready6, readyPC]
    simp [checkDispatchState, ready, signExtend13]
    split <;> simp_all
  rw [show 7 + fuel = 6 + (fuel + 1) by omega, check_dispatch_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem check_dispatch_registers (state : MachineState) :
    (checkDispatchState state).getReg .x26 = state.getReg .x11 ∧
    (checkDispatchState state).getReg .x24 = state.getReg .x13 ∧
    (checkDispatchState state).getReg .x8 = state.getReg .x14 ∧
    (checkDispatchState state).getReg .x25 = state.getReg .x15 ∧
    (checkDispatchState state).getReg .x27 = state.getReg .x16 ∧
    (checkDispatchState state).getReg .x16 = state.getReg .x16 ∧
    (checkDispatchState state).getReg .x17 = state.getReg .x17 ∧
    (checkDispatchState state).mem = state.mem := by
  dsimp only [checkDispatchState, checkDispatchPrefix, checkDispatchInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

/-! ### Normal length gate (`k ≠ 128`) and exit blocks -/

private def checkNormalLenInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 784]

private def checkNormalLenPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkNormalLenInstructions.take count).foldl execInstrBr state

private theorem check_normal_len_prefix (state : MachineState) (pc : state.pc = 4124)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkNormalLenPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := checkNormalLenPrefix state)
  intro i hi
  refine ⟨.base ((checkNormalLenInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (7 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The normal length gate compares `x16 * 784` with `x17` (after dispatch with `x16 ≠ 128`). -/
def checkLengthState (state : MachineState) : MachineState :=
  ((checkNormalLenPrefix (checkDispatchState state) 3).setReg .x7 (state.getReg .x16 * 784)).setPC
    (if state.getReg .x16 * 784 = state.getReg .x17 then 4144 else 4432)

/-- For `x16 ≠ 128`, 12 instructions and 15 cycles reach the normal length decision. -/
theorem check_length_gate (state : MachineState) (pc : state.pc = 4096)
    (not128 : state.getReg .x16 ≠ 128) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (12 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkLengthState state) allowCoins
          return result.charge 15 0) := by
  let disp := checkDispatchState state
  have dispPC : disp.pc = 4124 := if_neg not128
  let ready := checkNormalLenPrefix disp 3
  let multiplied := (ready.setReg .x7 (state.getReg .x16 * 784)).setPC 4140
  have readyPC : ready.pc = 4136 := by
    simp [ready, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, dispPC, MachineState.setPC]
  have fetched₁ : fetch (submission.image .check) ready = some (.base (.MUL .x7 .x16 .x6)) := by
    apply check_fetch ready 10 _ (by decide) readyPC; rfl
  have fetched₂ : fetch (submission.image .check) multiplied = some (.base (.BNE .x7 .x17 292)) := by
    apply check_fetch multiplied 11 _ (by decide) rfl; rfl
  have readyCount : ready.getReg .x16 = state.getReg .x16 := by
    have h := (check_dispatch_registers state).2.2.2.2.2.1
    simpa [ready, disp, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC] using h
  have readyLength : ready.getReg .x17 = state.getReg .x17 := by
    have h := (check_dispatch_registers state).2.2.2.2.2.2.1
    simpa [ready, disp, checkNormalLenPrefix, checkNormalLenInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC] using h
  have readyFactor : ready.getReg .x6 = 784 := by
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
    check_dispatch state pc, check_normal_len_prefix disp dispPC]
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
    execute (submission.image .check) (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure, checkExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 4424 else 4436)
  have fetch₁ : fetch (submission.image .check) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply check_fetch state 84 _ (by decide) pc; rfl
    · apply check_fetch state 81 _ (by decide) pc; rfl
  have fetch₂ : fetch (submission.image .check) next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply check_fetch next 85 _ (by decide) rfl; rfl
    · apply check_fetch next 82 _ (by decide) rfl; rfl
  have fetch₃ : fetch (submission.image .check) (checkExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply check_fetch _ 86 _ (by decide) rfl; rfl
    · apply check_fetch _ 83 _ (by decide) rfl; rfl
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
    (wrong : state.getReg .x16 * 784 ≠ state.getReg .x17)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (15 + fuel) state allowCoins =
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
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkScratchPrefix state 2) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := checkScratchPrefix state)
  intro i hi
  refine ⟨.base ((checkScratchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (12 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The three-instruction transition after a valid normal length. -/
theorem check_ready (state : MachineState) (pc : state.pc = 4144)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkReadyState state) allowCoins
          return result.charge 3 0) := by
  let ready := checkScratchPrefix state 2
  have readyPC : ready.pc = 4152 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x27 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have fetched : fetch (submission.image .check) ready = some (.base (.BEQ .x27 .x0 268)) := by
    apply check_fetch ready 14 _ (by decide) readyPC; rfl
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
    (checkLengthState state).mem = state.mem := by
  dsimp only [checkLengthState, checkNormalLenPrefix, checkNormalLenInstructions,
    checkDispatchState, checkDispatchPrefix, checkDispatchInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

/-- Register mapping after the normal input gate and scratch/depth initialization. -/
theorem check_ready_registers (state : MachineState) :
    (checkReadyState (checkLengthState state)).getReg .x21 = 256 ∧
    (checkReadyState (checkLengthState state)).getReg .x24 = state.getReg .x13 ∧
    (checkReadyState (checkLengthState state)).getReg .x8 = state.getReg .x14 ∧
    (checkReadyState (checkLengthState state)).getReg .x25 = state.getReg .x15 ∧
    (checkReadyState (checkLengthState state)).getReg .x26 = state.getReg .x11 ∧
    (checkReadyState (checkLengthState state)).getReg .x27 = state.getReg .x16 ∧
    (checkReadyState (checkLengthState state)).getReg .x30 = 24 := by
  dsimp only [checkReadyState, checkScratchPrefix, checkScratchInstructions,
    checkLengthState, checkNormalLenPrefix, checkNormalLenInstructions,
    checkDispatchState, checkDispatchPrefix, checkDispatchInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

theorem check_ready_pc (state : MachineState) :
    (checkReadyState (checkLengthState state)).pc =
      if state.getReg .x16 = 0 then 4420 else 4156 := by
  change (if (checkLengthState state).getReg .x27 = 0 then 4420 else 4156) = _
  rw [(check_length_preserves state).1]

private theorem run_check_valid (candidate : Submission) (input : CheckInput)
    (valid : input.proof.length ≤ candidate.sizes.proof) :
    candidate.run .check input = execute (candidate.image .check) (candidate.steps .check)
      (candidate.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]
  rfl

/-- Proofs beyond the declared capacity are rejected by the ABI before execution. -/
theorem check_oversized (input : CheckInput) (oversized : submission.sizes.proof < input.proof.length) :
    submission.run .check input = pure ⟨.failure, initialMachine, 0, 0⟩ := by
  have invalid : ¬input.proof.length ≤ submission.sizes.proof := by omega
  simp only [Submission.run, invalid, decide_false, Bool.false_eq_true, if_false]

/-- The 64-bit normal length comparison cannot wrap around for any admitted proof. -/
theorem check_input_length (input : CheckInput) (valid : input.proof.length ≤ submission.sizes.proof) :
    ((submission.initialState .check input).getReg .x16 * 784 =
      (submission.initialState .check input).getReg .x17) ↔
      input.proof.length = 784 * input.positions.card := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have countBound : input.positions.card < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have lengthBound : input.proof.length < 2^64 := by
    change input.proof.length ≤ 13153337344 at valid
    norm_num; omega
  have productBound : input.positions.card * 784 < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  change (BitVec.ofNat 64 input.positions.card * 784 = BitVec.ofNat 64 input.proof.length) ↔ _
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound,
    Nat.mod_eq_of_lt lengthBound]
  change (input.positions.card * 784) % 2^64 = input.proof.length ↔ _
  rw [Nat.mod_eq_of_lt productBound]
  omega

/-- Every in-capacity normal-mode malformed length rejects in 18 cycles and zero queries. -/
theorem check_input_wrong_length (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof)
    (notBatch : input.positions.card ≠ BATCH)
    (wrong : input.proof.length ≠ 784 * input.positions.card) :
    submission.run .check input =
      pure ⟨.failure, checkExitState (checkLengthState (submission.initialState .check input)) false,
        18, 0⟩ := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have countBound : input.positions.card < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have not128 : (submission.initialState .check input).getReg .x16 ≠ 128 := by
    intro h
    have n := congrArg BitVec.toNat h
    change input.positions.card % 2^64 = 128 at n
    rw [Nat.mod_eq_of_lt countBound] at n
    exact notBatch n
  have gateWrong : (submission.initialState .check input).getReg .x16 * 784 ≠
      (submission.initialState .check input).getReg .x17 :=
    fun matched => wrong ((check_input_length input valid).mp matched)
  have steps : submission.steps .check = 15 + (submission.steps .check - 15) := by
    change 214748365824 = 15 + (214748365824 - 15); rfl
  exact (run_check_valid submission input valid).trans
    ((congrArg (fun fuel => execute (submission.image .check) fuel
      (submission.initialState .check input) false) steps).trans
      (check_wrong_length _ rfl not128 gateWrong _ false))

/-! ### Four-word digest comparison (shared by `check-root` at 66 and `cap-root` at 138) -/

private def checkRootInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x21 (BitVec.ofNat 12 (8 * word)), .LD .x7 .x23 (BitVec.ofNat 12 (8 * word))]

private def checkRootPrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((checkRootInstructions word).take count).foldl execInstrBr state

private def checkRootBranchOffset (start word : Nat) : BitVec 13 :=
  BitVec.ofNat 13 ((if start = 66 then 64 else 7968) - 12 * word)

/-- Compare one of the four 64-bit words of `[x21, x21+32)` and `[x23, x23+32)`. -/
def checkRootWordState (state : MachineState) (start word : Nat) : MachineState :=
  execInstrBr (checkRootPrefix state word 2) (.BNE .x6 .x7 (checkRootBranchOffset start word))

theorem check_root_word (state : MachineState) (start word : Nat)
    (location : start = 66 ∨ start = 138) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkRootWordState state start word) allowCoins
          return result.charge 3 0) := by
  have loads (remaining : Nat) : execute (submission.image .check) (2 + remaining) state allowCoins =
      (do let result ← execute (submission.image .check) remaining
            (checkRootPrefix state word 2) allowCoins
          return result.charge 2 0) := by
    apply execute_unit_steps (states := checkRootPrefix state word)
    intro i hi
    refine ⟨.base (((checkRootInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply check_fetch _ (start + 3 * word + i) _ (by rcases location with rfl | rfl <;> omega)
      · rcases location with rfl | rfl <;> interval_cases word <;> interval_cases i <;>
          simp [checkRootPrefix, checkRootInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl <;> interval_cases word <;> interval_cases i <;> rfl
    · have offset : signExtend12 (BitVec.ofNat 12 (8 * word)) = BitVec.ofNat 64 (8 * word) := by
        interval_cases word <;> rfl
      interval_cases i <;>
        simp only [checkRootPrefix, checkRootInstructions, List.take, List.foldl,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, offset,
          MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23)] <;>
        first | rw [scratchValid]; rfl | rw [targetValid]; rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .check) (checkRootPrefix state word 2) =
      some (.base (.BNE .x6 .x7 (checkRootBranchOffset start word))) := by
    apply check_fetch _ (start + 3 * word + 2) _ (by rcases location with rfl | rfl <;> omega)
    · rcases location with rfl | rfl <;> interval_cases word <;>
        simp [checkRootPrefix, checkRootInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl <;> interval_cases word <;> rfl
  have stepped : ordinaryStep (checkRootPrefix state word 2)
      (.base (.BNE .x6 .x7 (checkRootBranchOffset start word))) =
        some (checkRootWordState state start word) := rfl
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, loads]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem check_root_word_preserves (state : MachineState) (start word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordState state start word).getReg reg = state.getReg reg ∧
    (checkRootWordState state start word).mem = state.mem := by
  constructor
  · simp only [checkRootWordState, checkRootPrefix, checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> simp only [MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLeft),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notRight)]
  · simp only [checkRootWordState, checkRootPrefix, checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> rfl

theorem check_root_word_pc (state : MachineState) (start word : Nat)
    (location : start = 66 ∨ start = 138) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word)) :
    (checkRootWordState state start word).pc =
      if state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
          state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) then
        BitVec.ofNat 64 (4096 + 4 * start + 12 * (word + 1)) else 4432 := by
  rcases location with rfl | rfl <;> interval_cases word <;>
    simp [checkRootWordState, checkRootPrefix, checkRootInstructions, checkRootBranchOffset,
      execInstrBr, signExtend12, signExtend13, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, MachineState.getMem, pc] <;>
    split <;> simp_all

theorem check_root_word_reject (state : MachineState) (start word : Nat)
    (location : start = 66 ∨ start = 138) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkRootWordState state start word) false, 6, 0⟩ := by
  have rejectPC : (checkRootWordState state start word).pc = 4432 := by
    rw [check_root_word_pc state start word location bounded pc, if_neg different]
  rw [show 6 + fuel = 3 + (3 + fuel) by omega,
    check_root_word state start word location bounded pc scratchValid targetValid,
    check_exit _ false rejectPC]
  simp [Execution.charge]

def checkRootWordsState (state : MachineState) (start : Nat) : Nat → MachineState
  | 0 => state
  | count + 1 => checkRootWordState (checkRootWordsState state start count) start count

theorem check_root_words_preserves (state : MachineState) (start count : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordsState state start count).getReg reg = state.getReg reg ∧
    (checkRootWordsState state start count).mem = state.mem := by
  induction count with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    have preserved := check_root_word_preserves (checkRootWordsState state start count)
      start count reg notLeft notRight
    exact ⟨preserved.1.trans ih.1, preserved.2.trans ih.2⟩

private theorem check_root_words_read (state : MachineState) (start count word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordsState state start count).getMem
        ((checkRootWordsState state start count).getReg reg + BitVec.ofNat 64 (8 * word)) =
      state.getMem (state.getReg reg + BitVec.ofNat 64 (8 * word)) := by
  have preserved := check_root_words_preserves state start count reg notLeft notRight
  rw [preserved.1]
  exact congrFun preserved.2 _

theorem check_root_words_pc (state : MachineState) (start : Nat)
    (location : start = 66 ∨ start = 138)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (count : Nat) (bounded : count ≤ 4)
    (agrees : ∀ word < count,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word))) :
    (checkRootWordsState state start count).pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * count) := by
  induction count with
  | zero => exact pc
  | succ count ih =>
    have previous := ih (by omega) (fun word bound => agrees word (by omega))
    rw [checkRootWordsState, check_root_word_pc _ start count location (by omega) previous,
      check_root_words_read state start count count .x21 (by decide) (by decide),
      check_root_words_read state start count count .x23 (by decide) (by decide),
      if_pos (agrees count (by omega))]

theorem check_root_prefix (state : MachineState) (start : Nat)
    (location : start = 66 ∨ start = 138)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (count : Nat) (bounded : count ≤ 4)
    (agrees : ∀ word < count,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (remaining : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 * count + remaining) state allowCoins =
      (do let result ← execute (submission.image .check) remaining
            (checkRootWordsState state start count) allowCoins
          return result.charge (3 * count) 0) := by
  induction count generalizing remaining with
  | zero => simp [checkRootWordsState, Execution.charge]
  | succ count ih =>
    have position := check_root_words_pc state start location pc count (by omega)
      (fun word bound => agrees word (by omega))
    have scratch : accessValid ((checkRootWordsState state start count).getReg .x21 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(check_root_words_preserves state start count .x21 (by decide) (by decide)).1]
      exact scratchValid count (by omega)
    have target : accessValid ((checkRootWordsState state start count).getReg .x23 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(check_root_words_preserves state start count .x23 (by decide) (by decide)).1]
      exact targetValid count (by omega)
    rw [show 3 * (count + 1) + remaining = 3 * count + (3 + remaining) by omega,
      ih (by omega) (fun word bound => agrees word (by omega)),
      check_root_word _ start count location (by omega) position scratch target]
    simp [checkRootWordsState, Execution.charge, Nat.mul_add, ← Nat.add_assoc]

theorem check_root_matches (state : MachineState) (start : Nat)
    (location : start = 66 ∨ start = 138)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (agrees : ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (12 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkRootWordsState state start 4) allowCoins
          return result.charge 12 0) :=
  check_root_prefix state start location pc scratchValid targetValid 4 (by decide) agrees fuel allowCoins

theorem check_root_first_mismatch (state : MachineState) (start : Nat)
    (location : start = 66 ∨ start = 138)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (word : Nat) (bounded : word < 4)
    (earlier : ∀ index < word,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * index)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * index)))
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 * word + 6 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkRootWordState (checkRootWordsState state start word) start word) false,
        3 * word + 6, 0⟩ := by
  have prefixPC := check_root_words_pc state start location pc word (by omega) earlier
  have scratchReg := (check_root_words_preserves state start word .x21 (by decide) (by decide)).1
  have targetPreserves := check_root_words_preserves state start word .x23 (by decide) (by decide)
  have targetReg := targetPreserves.1
  have scratchAccess : accessValid ((checkRootWordsState state start word).getReg .x21 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [scratchReg]; exact scratchValid word bounded
  have targetAccess : accessValid ((checkRootWordsState state start word).getReg .x23 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [targetReg]; exact targetValid word bounded
  have mismatch : (checkRootWordsState state start word).getMem
        ((checkRootWordsState state start word).getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      (checkRootWordsState state start word).getMem
        ((checkRootWordsState state start word).getReg .x23 + BitVec.ofNat 64 (8 * word)) := by
    simpa only [scratchReg, targetReg, MachineState.getMem, targetPreserves.2] using different
  rw [Nat.add_assoc, check_root_prefix state start location pc scratchValid targetValid word (by omega) earlier,
    check_root_word_reject _ start word location bounded prefixPC scratchAccess targetAccess mismatch]
  simp [Execution.charge, Nat.add_comm]

/-- If any digest word differs, comparison halts with failure within 15 cycles. -/
theorem check_root_rejects (state : MachineState) (start : Nat)
    (location : start = 66 ∨ start = 138)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : ¬ ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    ∃ result, execute (submission.image .check) (15 + fuel) state allowCoins = pure result ∧
      result.exit = .failure ∧ result.cycles ≤ 15 ∧ result.oracleCalls = 0 := by
  have existsMismatch : ∃ word, word < 4 ∧
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) := by
    push Not at different
    exact different
  let word := Nat.find existsMismatch
  have bounded : word < 4 := (Nat.find_spec existsMismatch).1
  have mismatch := (Nat.find_spec existsMismatch).2
  have earlier : ∀ index < word,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * index)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * index)) := by
    intro index before
    have minimal := Nat.find_min existsMismatch before
    exact Classical.byContradiction (fun neq => minimal ⟨by omega, neq⟩)
  refine ⟨⟨.failure, checkExitState (checkRootWordState (checkRootWordsState state start word) start word) false,
    3 * word + 6, 0⟩, ?_, rfl, by dsimp; omega, rfl⟩
  have remaining : 15 + fuel = 3 * word + 6 + (9 - 3 * word + fuel) := by omega
  rw [remaining]
  exact check_root_first_mismatch state start location pc scratchValid targetValid word bounded
    earlier mismatch _ allowCoins

/-! ### Path compression call (`check-compress`, start = 54) -/

private def checkCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def checkCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkCompressionInstructions.take count).foldl execInstrBr state

def checkCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  let ready := checkCompressionPrefix state 5
  writeBits ((savePaddingRegisters (ready.setReg .x31 (ready.pc+4))).setReg .x11 64) 256 answer

theorem check_compression (state : MachineState) (start : Nat)
    (location : start = 54)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (22 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer state 256 64))))
          let result ← execute (submission.image .check) fuel (checkCompressionState state answer) allowCoins
          return result.charge 29 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .check) (5 + remaining) state allowCoins =
        (do let result ← execute (submission.image .check) remaining
              (checkCompressionPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := checkCompressionPrefix state)
    intro i hi
    refine ⟨.base ((checkCompressionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply check_fetch _ (start + i) _ (by rcases location with rfl <;> omega)
      · rcases location with rfl <;> interval_cases i <;>
          simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := checkCompressionPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (start+5)) := by
    dsimp only [ready]
    rcases location with rfl <;>
        simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 64 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 := by
    simp [ready, checkCompressionPrefix, checkCompressionInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, scratch]
    rfl
  have call := padding_call true ready (start+5) (by rcases location with rfl; exact Or.inl rfl) readyPC
    registers.1 registers.2.2.2.2
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1, registers.2.2.2.1]; decide) fuel allowCoins
  simp only [paddingProgram, ↓reduceIte] at call
  rw [show 22 + fuel = 5 + (17 + fuel) by omega, setup]
  erw [call]
  simp only [bind_assoc, pure_bind]
  rw [registers.2.1]
  change ((liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64)))))) >>= _) = _
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have resultState : paddedCompressionState ready answer = checkCompressionState state answer := by
    unfold paddedCompressionState
    rw [registers.2.2.2.1]
    rfl
  rw [resultState]
  simp [Execution.charge, ← Nat.add_assoc]

theorem check_compression_pc (state : MachineState) (answer : BitVec 256) :
    (checkCompressionState state answer).pc = state.pc + 24 := by
  simp [checkCompressionState, writeBits, savePaddingRegisters, checkCompressionPrefix, checkCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem check_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
    (not14 : reg ≠ .x14 := by decide) (not15 : reg ≠ .x15 := by decide)
    (not16 : reg ≠ .x16 := by decide) (not17 : reg ≠ .x17 := by decide)
    (not31 : reg ≠ .x31 := by decide) :
    (checkCompressionState state answer).getReg reg = state.getReg reg := by
  rw [checkCompressionState, writeBits_register]
  simp only [savePaddingRegisters, checkCompressionPrefix, checkCompressionInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not14),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not15),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not16),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not17),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not31)]

set_option maxHeartbeats 2000000 in
theorem check_compression_word (state : MachineState) (answer : BitVec 256)
    (word : Nat) (bounded : word < 4) :
    (checkCompressionState state answer).getMem (BitVec.ofNat 64 (256 + 8 * word)) =
      answer.extractLsb' (64 * word) 64 := by
  have byte (i : Nat) : BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)) =
      answer.extractLsb' (8 * i) 8 := by
    apply BitVec.toNat_inj.mp
    simp [Nat.shiftRight_eq_div_pow]
  unfold checkCompressionState writeBits
  simp_rw [byte]
  interval_cases word <;>
    simp [List.range_succ, MachineState.setPC, MachineState.setByte,
      MachineState.setMem, MachineState.getMem, alignToDword, byteOffset, replaceByte] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;>
    interval_cases bit <;>
    simp

theorem check_compression_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkCompressionState state answer).getMem address = state.getMem address := by
  unfold checkCompressionState
  rw [writeBits_memory_outside]
  · rfl
  · intro i hi
    change i < 32 at hi
    interval_cases i <;> norm_num [alignToDword] <;> tauto

/-! ### Direct 96-byte leaf compression (used by Call 0 at 172 and loop at 196) -/

/-- The compression input of a leaf call: 96 bytes of scratch. -/
def leafQuery (state : MachineState) : BitVec COMPRESSION_INPUT_LENGTH := readBuffer state 256 96

private def checkLeafCallInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 96,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def checkLeafCallPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkLeafCallInstructions.take count).foldl execInstrBr state

def checkLeafCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (checkLeafCallPrefix state 5) 256 answer

private theorem check_leaf_call_registers (state : MachineState) (scratch : state.getReg .x21 = 256) :
    (checkLeafCallPrefix state 5).getReg .x5 = 0 ∧ (checkLeafCallPrefix state 5).getReg .x10 = 256 ∧
      (checkLeafCallPrefix state 5).getReg .x11 = 96 ∧ (checkLeafCallPrefix state 5).getReg .x12 = 256 ∧
      (checkLeafCallPrefix state 5).getReg .x13 = 0 := by
  simp [checkLeafCallPrefix, checkLeafCallInstructions, execInstrBr,
    signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne, scratch]
  rfl

set_option maxHeartbeats 1600000 in
/-- A direct 96-byte compression of scratch at either Call 0 (`start = 172`, `pc = 4784`)
or the 3-block loop (`start = 196`, `pc = 4880`). -/
theorem check_leaf_compression (state : MachineState) (start : Nat)
    (location : start = 172 ∨ start = 196)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery state)))
          let result ← execute (submission.image .check) fuel
            (checkLeafCompressionState state answer) allowCoins
          return result.charge 13 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .check) (5 + remaining) state allowCoins =
        (do let result ← execute (submission.image .check) remaining
              (checkLeafCallPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := checkLeafCallPrefix state)
    intro i hi
    refine ⟨.base ((checkLeafCallInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply check_fetch _ (start + i) _ (by rcases location with rfl | rfl <;> omega)
      · rcases location with rfl | rfl <;> interval_cases i <;>
          simp [checkLeafCallPrefix, checkLeafCallInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := checkLeafCallPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (start + 5)) := by
    dsimp only [ready]
    rcases location with rfl | rfl <;>
      simp [checkLeafCallPrefix, checkLeafCallInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 96 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 :=
    check_leaf_call_registers state scratch
  have fetched : fetch (submission.image .check) ready = some (.base .ECALL) := by
    apply check_fetch _ (start + 5) _ (by rcases location with rfl | rfl <;> omega) readyPC
    rcases location with rfl | rfl <;> rfl
  have input : oracleInput ready = some (.inl (leafQuery state)) := by
    have sameMem (address : Word) : ready.getMem address = state.getMem address := rfl
    have memory : readBuffer ready 256 96 = readBuffer state 256 96 := by
      unfold readBuffer
      simp only [MachineState.getByte, sameMem]
    have kind := registers.2.2.2.2
    simp [oracleInput, registers.2.1, registers.2.2.1, registers.2.2.2.1, kind,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, MEMORY_BYTES]
    rw [memory]
    rfl
  rw [show 6 + fuel = 5 + (fuel + 1) by omega, setup, execute, fetched, if_pos registers.1, input]
  simp only [writeOracleAnswer, registers.2.2.2.1, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery state)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have r12 : (checkLeafCallPrefix state 5).getReg .x12 = 256 := registers.2.2.2.1
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, checkLeafCompressionState, r12,
    ← Nat.add_assoc]
  congr

theorem check_leaf_compression_pc (state : MachineState) (answer : BitVec 256) :
    (checkLeafCompressionState state answer).pc = state.pc + 24 := by
  simp [checkLeafCompressionState, writeBits, checkLeafCallPrefix, checkLeafCallInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem check_leaf_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
    (checkLeafCompressionState state answer).getReg reg = state.getReg reg := by
  rw [checkLeafCompressionState, writeBits_register]
  simp only [checkLeafCallPrefix, checkLeafCallInstructions, List.take, List.foldl, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13)]

theorem check_leaf_compression_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkLeafCompressionState state answer).getMem address = state.getMem address := by
  unfold checkLeafCompressionState
  rw [writeBits_memory_outside]
  · rfl
  · intro i hi
    change i < 32 at hi
    interval_cases i <;> norm_num [alignToDword] <;> tauto

/-! ### Call 0 of `leafSubroutine`: 9-word head copy (154..171), Call 0 (172..177), post (178..179) -/

private def checkLeafInitCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 24, .LD .x6 .x8 8, .SD .x21 .x6 32,
   .LD .x6 .x8 16, .SD .x21 .x6 40, .LD .x6 .x8 24, .SD .x21 .x6 48,
   .LD .x6 .x8 32, .SD .x21 .x6 56, .LD .x6 .x8 40, .SD .x21 .x6 64,
   .LD .x6 .x8 48, .SD .x21 .x6 72, .LD .x6 .x8 56, .SD .x21 .x6 80,
   .LD .x6 .x8 64, .SD .x21 .x6 88]

private def checkLeafInitCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkLeafInitCopyInstructions.take count).foldl execInstrBr state

def checkLeafInitCopyState (state : MachineState) : MachineState := checkLeafInitCopyPrefix state 18

theorem check_leaf_init_copy_expansion (state : MachineState) :
    checkLeafInitCopyState state =
      ([.LD .x6 .x8 0, .SD .x21 .x6 24, .LD .x6 .x8 8, .SD .x21 .x6 32,
        .LD .x6 .x8 16, .SD .x21 .x6 40, .LD .x6 .x8 24, .SD .x21 .x6 48,
        .LD .x6 .x8 32, .SD .x21 .x6 56, .LD .x6 .x8 40, .SD .x21 .x6 64,
        .LD .x6 .x8 48, .SD .x21 .x6 72, .LD .x6 .x8 56, .SD .x21 .x6 80,
        .LD .x6 .x8 64, .SD .x21 .x6 88] : List Instr).foldl execInstrBr state := rfl

private theorem check_init_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 18)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (checkLeafInitCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [checkLeafInitCopyPrefix, checkLeafInitCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem check_leaf_init_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (checkLeafInitCopyState state).getReg reg = state.getReg reg :=
  check_init_copy_register state 18 (by decide) reg scratch

set_option maxHeartbeats 2000000 in
/-- Copy the first 72 message bytes behind `[salt(16B) || tag(8B)]` in scratch `[280, 352)`. -/
theorem check_leaf_init_copy (state : MachineState) (pc : state.pc = 4712)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (18 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafInitCopyState state) allowCoins
          return result.charge 18 0) := by
  apply execute_unit_steps (states := checkLeafInitCopyPrefix state)
  intro i hi
  refine ⟨.base ((checkLeafInitCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (154 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkLeafInitCopyPrefix, checkLeafInitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := check_init_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (check_init_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have s4 := sourceValid ⟨4, by decide⟩
    have s5 := sourceValid ⟨5, by decide⟩
    have s6 := sourceValid ⟨6, by decide⟩
    have s7 := sourceValid ⟨7, by decide⟩
    have s8 := sourceValid ⟨8, by decide⟩
    have valid : memoryArgumentsValid (checkLeafInitCopyPrefix state i)
        ((checkLeafInitCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [checkLeafInitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · exact s2
      · rfl
      · exact s3
      · rfl
      · exact s4
      · rfl
      · exact s5
      · rfl
      · exact s6
      · rfl
      · exact s7
      · rfl
      · exact s8
      · rfl
    interval_cases i <;>
      simp only [checkLeafInitCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Advance `x8 += 64` and initialize `x28 := 3` before the 3-block tail loop (indices 178..179). -/
def checkLeafInitPostState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 64)).setReg .x28 3).setPC 4816

theorem check_leaf_init_post (state : MachineState) (pc : state.pc = 4808)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafInitPostState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x8 (state.getReg .x8 + 64)).setPC 4812
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x8 .x8 64)) := by
    apply check_fetch _ 178 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.ADDI .x28 .x0 3)) := by
    apply check_fetch _ 179 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 64)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, next]
  have s1 : ordinaryStep next (.base (.ADDI .x28 .x0 3)) = some (checkLeafInitPostState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next,
      checkLeafInitPostState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- State entering `leaf-block` after Call 0 completes (with `x8 += 64`, `x28 = 3`, `pc = 4816`). -/
def checkLeafInitStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkLeafInitPostState (checkLeafCompressionState (checkLeafInitCopyState state) answer)

theorem check_leaf_init (state : MachineState) (pc : state.pc = 4712)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (26 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))
          let result ← execute (submission.image .check) fuel (checkLeafInitStepState state answer) allowCoins
          return result.charge 33 1) := by
  have copyPC : (checkLeafInitCopyState state).pc = BitVec.ofNat 64 (4096 + 4 * 172) := by
    simp [checkLeafInitCopyState, checkLeafInitCopyPrefix, checkLeafInitCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (checkLeafInitCopyState state).getReg .x21 = 256 :=
    (check_init_copy_register state 18 (by decide) .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkLeafCompressionState (checkLeafInitCopyState state) answer).pc = 4808 := by
    rw [check_leaf_compression_pc, copyPC]; rfl
  rw [show 26 + fuel = 18 + (6 + (2 + fuel)) by omega,
    check_leaf_init_copy state pc scratch sourceValid,
    check_leaf_compression _ 172 (Or.inl rfl) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  rw [check_leaf_init_post _ (compressionPC answer)]
  simp [checkLeafInitStepState, Execution.charge, ← Nat.add_assoc]

theorem check_leaf_init_registers (state : MachineState) (answer : BitVec 256) :
    (checkLeafInitStepState state answer).getReg .x8 = state.getReg .x8 + 64 ∧
    (checkLeafInitStepState state answer).getReg .x28 = 3 ∧
    (checkLeafInitStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (checkLeafInitStepState state answer).getReg .x1 = state.getReg .x1 ∧
    (checkLeafInitStepState state answer).pc = 4816 := by
  have preserved (reg : Reg) (safe : reg ∈ [Reg.x8, .x21, .x1]) :
      (checkLeafCompressionState (checkLeafInitCopyState state) answer).getReg reg = state.getReg reg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at safe
    rcases safe with rfl | rfl | rfl <;>
      exact (check_leaf_compression_register _ answer _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans (check_init_copy_register state 18 (by decide) _ (by decide))
  simp only [checkLeafInitStepState, checkLeafInitPostState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x1),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by simp), preserved .x21 (by simp), preserved .x1 (by simp)]
  exact ⟨rfl, trivial, rfl, rfl, rfl⟩

private theorem check_leaf_init_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31]) :
    (checkLeafInitStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28, not14, not15, not16, not17, not31⟩
  simp only [checkLeafInitStepState, checkLeafInitPostState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (check_leaf_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (check_init_copy_register state 18 (by decide) reg not6)

/-! ### Three-block tail loop (`leaf-block` at index 180, `pc = 4816`) -/

private def checkLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56,
   .LD .x6 .x8 32, .SD .x21 .x6 64, .LD .x6 .x8 40, .SD .x21 .x6 72,
   .LD .x6 .x8 48, .SD .x21 .x6 80, .LD .x6 .x8 56, .SD .x21 .x6 88]

private def checkLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkLeafCopyInstructions.take count).foldl execInstrBr state

def checkLeafCopyState (state : MachineState) : MachineState := checkLeafCopyPrefix state 16

theorem check_leaf_copy_expansion (state : MachineState) :
    checkLeafCopyState state =
      ([.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
        .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56,
        .LD .x6 .x8 32, .SD .x21 .x6 64, .LD .x6 .x8 40, .SD .x21 .x6 72,
        .LD .x6 .x8 48, .SD .x21 .x6 80, .LD .x6 .x8 56, .SD .x21 .x6 88] : List Instr).foldl
          execInstrBr state := rfl

private theorem check_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 16)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (checkLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [checkLeafCopyPrefix, checkLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem check_leaf_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (checkLeafCopyState state).getReg reg = state.getReg reg :=
  check_copy_register state 16 (by decide) reg scratch

set_option maxHeartbeats 1600000 in
theorem check_leaf_copy (state : MachineState) (pc : state.pc = 4816)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (16 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCopyState state) allowCoins
          return result.charge 16 0) := by
  apply execute_unit_steps (states := checkLeafCopyPrefix state)
  intro i hi
  refine ⟨.base ((checkLeafCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (180 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkLeafCopyPrefix, checkLeafCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := check_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (check_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have s4 := sourceValid ⟨4, by decide⟩
    have s5 := sourceValid ⟨5, by decide⟩
    have s6 := sourceValid ⟨6, by decide⟩
    have s7 := sourceValid ⟨7, by decide⟩
    have valid : memoryArgumentsValid (checkLeafCopyPrefix state i)
        ((checkLeafCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [checkLeafCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · exact s2
      · rfl
      · exact s3
      · rfl
      · exact s4
      · rfl
      · exact s5
      · rfl
      · exact s6
      · rfl
      · exact s7
      · rfl
    interval_cases i <;>
      simp only [checkLeafCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The leaf-loop latch advances by one 64-byte block, then decrements the counter. -/
def checkLeafNextState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 64)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4916 else 4816)

theorem check_leaf_next (state : MachineState) (pc : state.pc = 4904)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafNextState state) allowCoins
          return result.charge 3 0) := by
  let advanced := (state.setReg .x8 (state.getReg .x8 + 64)).setPC 4908
  let next := (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 4912
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x8 .x8 64)) := by
    apply check_fetch _ 202 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply check_fetch _ 203 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) next = some (.base (.BNE .x28 .x0 8096)) := by
    apply check_fetch _ 204 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 64)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep next (.base (.BNE .x28 .x0 8096)) = some (checkLeafNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, checkLeafNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def checkLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkLeafNextState (checkLeafCompressionState (checkLeafCopyState state) answer)

theorem check_leaf_block (state : MachineState) (pc : state.pc = 4816)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (25 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))
          let result ← execute (submission.image .check) fuel (checkLeafStepState state answer) allowCoins
          return result.charge 32 1) := by
  have copyPC : (checkLeafCopyState state).pc = BitVec.ofNat 64 (4096 + 4 * 196) := by
    simp [checkLeafCopyState, checkLeafCopyPrefix, checkLeafCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (checkLeafCopyState state).getReg .x21 = 256 :=
    (check_copy_register state 16 (by decide) .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkLeafCompressionState (checkLeafCopyState state) answer).pc = 4904 := by
    rw [check_leaf_compression_pc, copyPC]
    rfl
  rw [show 25 + fuel = 16 + (6 + (3 + fuel)) by omega, check_leaf_copy state pc scratch sourceValid,
    check_leaf_compression _ 196 (Or.inr rfl) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  rw [check_leaf_next _ (compressionPC answer)]
  simp [checkLeafStepState, Execution.charge, ← Nat.add_assoc]

theorem check_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (checkLeafStepState state answer).getReg .x8 = state.getReg .x8 + 64 ∧
    (checkLeafStepState state answer).getReg .x28 = state.getReg .x28 - 1 ∧
    (checkLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (checkLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (safe : reg ∈ [Reg.x8, .x28, .x21, .x1]) :
      (checkLeafCompressionState (checkLeafCopyState state) answer).getReg reg = state.getReg reg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at safe
    rcases safe with rfl | rfl | rfl | rfl <;>
      exact (check_leaf_compression_register _ answer _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans (check_copy_register state 16 (by decide) _ (by decide))
  simp only [checkLeafStepState, checkLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x1),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by simp),
    preserved .x28 (by simp),
    preserved .x21 (by simp),
    preserved .x1 (by simp)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem check_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (checkLeafStepState state answer).pc =
      if state.getReg .x28 - 1 = 0 then 4916 else 4816 := by
  change (if (checkLeafCompressionState (checkLeafCopyState state) answer).getReg .x28 - 1 = 0
    then 4916 else 4816) = _
  rw [check_leaf_compression_register _ answer .x28 (by decide) (by decide) (by decide) (by decide) (by decide),
    checkLeafCopyState, check_copy_register state 16 (by decide) .x28 (by decide)]

def checkLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))
      checkLeafLoop (checkLeafStepState state answer) count

theorem check_leaf_loop (state : MachineState) (count : Nat) (bounded : count ≤ 3)
    (pc : 0 < count → state.pc = 4816) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 8 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (25 * count + fuel) state allowCoins =
      (do let finished ← checkLeafLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (32 * count) count) := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 8) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (checkLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (checkLeafStepState state answer).pc = 4816 := by
      rw [check_leaf_block_pc]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (check_leaf_block_registers state answer).2.1, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 8 * count) :
        accessValid ((checkLeafStepState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 8) (by omega)
      rw [(check_leaf_block_registers state answer).1]
      have address : state.getReg .x8 + 64 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 8)) := by
        rw [show 8 * (word + 8) = 64 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 25 * (count + 1) + fuel = 25 + (25 * count + fuel) by omega,
      check_leaf_block state (pc (by omega)) scratch currentValid]
    simp only [checkLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (leafQuery (checkLeafCopyState state))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    change BitVec 256 at answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((check_leaf_block_registers state answer).2.2.1.trans scratch) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem check_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 3)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (checkLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4916) := by
  induction count generalizing state with
  | zero =>
    simp only [checkLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
    simp only [checkLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have nextCounter : (checkLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have remaining := ih _ (by omega) nextCounter reached
    refine ⟨remaining.1, remaining.2.1.trans (check_leaf_block_registers state answer).2.2.2, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [checkLeafLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [check_leaf_block_pc state answer, counter]
      rfl
    · exact remaining.2.2 (by omega)

theorem check_leaf_return (state : MachineState) (pc : state.pc = 4916)
    (link : state.getReg .x1 = 4200) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (state.setPC 4200) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply check_fetch _ 205 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4200) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Semantic unfolding of `leafSubroutine`: Call 0 (`salt || tag || head72`), then 3 tail blocks. -/
def checkLeafSubroutineRun (state : MachineState) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))
  checkLeafLoop (checkLeafInitStepState state answer) 3

/-- The full 2048-bit tagged leaf-hashing subroutine: 102 instructions, 130 cycles, 4 queries. -/
theorem check_leaf_subroutine (state : MachineState) (pc : state.pc = 4712)
    (link : state.getReg .x1 = 4200) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (102 + fuel) state allowCoins =
      (do let finished ← checkLeafSubroutineRun state
          let result ← execute (submission.image .check) fuel (finished.setPC 4200) allowCoins
          return result.charge 130 4) := by
  have initSource : ∀ word : Fin 9,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => sourceValid word.val (by omega)
  rw [show 102 + fuel = 26 + (25 * 3 + (1 + fuel)) by omega,
    check_leaf_init state pc scratch initSource]
  simp only [checkLeafSubroutineRun, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery (checkLeafInitCopyState state))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have iregs := check_leaf_init_registers state answer
  have loopSource : ∀ word < 8 * 3,
      accessValid ((checkLeafInitStepState state answer).getReg .x8 +
        BitVec.ofNat 64 (8 * word)) 8 = true := by
    intro word hw
    rw [iregs.1]
    have address : state.getReg .x8 + 64 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 8)) := by
      rw [show 8 * (word + 8) = 64 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [address]
    exact sourceValid (word + 8) (by omega)
  rw [check_leaf_loop (checkLeafInitStepState state answer) 3 (by decide)
    (fun _ => iregs.2.2.2.2) iregs.2.1 (iregs.2.2.1.trans scratch) loopSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := check_leaf_loop_finished _ 3 (by decide) iregs.2.1 finished reachable
  have finalLink : finished.getReg .x1 = 4200 := done.2.1.trans (iregs.2.2.2.1.trans link)
  rw [check_leaf_return finished (done.2.2 (by decide)) finalLink]
  simp [Execution.charge, ← Nat.add_assoc]

private theorem check_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31]) :
    (checkLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28, not14, not15, not16, not17, not31⟩
  simp only [checkLeafStepState, checkLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (check_leaf_compression_register _ answer reg not5 not10 not11 not12 not13).trans
    (check_copy_register state 16 (by decide) reg not6)

theorem check_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (checkLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (64 * count) ∧
    ∀ reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [checkLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [checkLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have rest := ih _ reached
    constructor
    · rw [rest.1, (check_leaf_block_registers state answer).1]
      rw [show 64 * (count + 1) = 64 + 64 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (check_leaf_block_preserves state answer reg preserved)

theorem check_leaf_subroutine_registers (state finished : MachineState)
    (reachable : finished ∈ support (checkLeafSubroutineRun state)) :
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    ∀ reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  simp only [checkLeafSubroutineRun, mem_support_bind_iff] at reachable
  obtain ⟨answer, _, reached⟩ := reachable
  change BitVec 256 at answer
  have lregs := check_leaf_loop_registers _ 3 finished reached
  have iregs := check_leaf_init_registers state answer
  constructor
  · rw [lregs.1, iregs.1, BitVec.add_assoc]; rfl
  · intro reg preserved
    exact (lregs.2 reg preserved).trans (check_leaf_init_preserves state answer reg preserved)

private theorem leaf_init_copy_mem_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkLeafInitCopyState state).getMem address = state.getMem address := by
  have regSetMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  rw [check_leaf_init_copy_expansion]
  have o3 : address ≠ 280#64 := outside 3 (by decide)
  have o4 : address ≠ 288#64 := outside 4 (by decide)
  have o5 : address ≠ 296#64 := outside 5 (by decide)
  have o6 : address ≠ 304#64 := outside 6 (by decide)
  have o7 : address ≠ 312#64 := outside 7 (by decide)
  have o8 : address ≠ 320#64 := outside 8 (by decide)
  have o9 : address ≠ 328#64 := outside 9 (by decide)
  have o10 : address ≠ 336#64 := outside 10 (by decide)
  have o11 : address ≠ 344#64 := outside 11 (by decide)
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [regSetMem, scratch, o3, o4, o5, o6, o7, o8, o9, o10, o11,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq]

private theorem leaf_copy_mem_outside (state : MachineState) (address : Word)
    (scratch : state.getReg .x21 = 256)
    (outside : ∀ j < 8, address ≠ BitVec.ofNat 64 (288 + 8 * j)) :
    (checkLeafCopyState state).getMem address = state.getMem address := by
  have regSetMem (s : MachineState) (a v : Word) (r : Reg) : (s.setMem a v).getReg r = s.getReg r := by
    cases r <;> rfl
  rw [check_leaf_copy_expansion]
  have o0 : address ≠ 288#64 := outside 0 (by decide)
  have o1 : address ≠ 296#64 := outside 1 (by decide)
  have o2 : address ≠ 304#64 := outside 2 (by decide)
  have o3 : address ≠ 312#64 := outside 3 (by decide)
  have o4 : address ≠ 320#64 := outside 4 (by decide)
  have o5 : address ≠ 328#64 := outside 5 (by decide)
  have o6 : address ≠ 336#64 := outside 6 (by decide)
  have o7 : address ≠ 344#64 := outside 7 (by decide)
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [regSetMem, scratch, o0, o1, o2, o3, o4, o5, o6, o7, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

/-- Every supported run of the leaf tail loop preserves all memory outside `[256, 352)`. -/
theorem check_leaf_loop_support_outside (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (checkLeafLoop state count))
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    finished.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero =>
    simp only [checkLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished; rfl
  | succ count ih =>
    simp only [checkLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    rw [ih _ reached ((check_leaf_block_registers state answer).2.2.1.trans scratch)]
    change (checkLeafCompressionState (checkLeafCopyState state) answer).getMem address = _
    rw [check_leaf_compression_memory_outside _ _ _
      ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩]
    apply leaf_copy_mem_outside _ _ scratch
    intro j hj
    simpa only [show 256 + 8 * (j + 4) = 288 + 8 * j by omega] using outside (j + 4) (by omega)

/-- Every supported run of `checkLeafSubroutineRun` preserves all memory outside `[256, 352)`. -/
theorem check_leaf_subroutine_support_outside (state finished : MachineState)
    (reachable : finished ∈ support (checkLeafSubroutineRun state))
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    finished.getMem address = state.getMem address := by
  simp only [checkLeafSubroutineRun, mem_support_bind_iff] at reachable
  obtain ⟨answer, _, reached⟩ := reachable
  change BitVec 256 at answer
  rw [check_leaf_loop_support_outside _ 3 finished reached address
    ((check_leaf_init_registers state answer).2.2.1.trans scratch) outside]
  change (checkLeafCompressionState (checkLeafInitCopyState state) answer).getMem address = _
  rw [check_leaf_compression_memory_outside _ _ _
    ⟨outside 0 (by decide), outside 1 (by decide), outside 2 (by decide), outside 3 (by decide)⟩]
  exact leaf_init_copy_mem_outside state address scratch outside

end CommitGolfCandidate
