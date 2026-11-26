import CommitGolfCandidate.Padding96Call

/-! The checker’s input gate and exit blocks, proved against the submitted image.
Malformed proof lengths reject before any oracle call or proof-memory access. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem check_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 200) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
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

private def checkSetupInstructions : List Instr :=
  [.ADDI .x26 .x11 0, .ADDI .x24 .x13 0, .ADDI .x8 .x14 0,
   .ADDI .x25 .x15 0, .ADDI .x27 .x16 0, .ADDI .x6 .x0 0,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 800]

private def checkSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkSetupInstructions.take count).foldl execInstrBr state

private theorem check_setup_prefix (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkSetupPrefix state 8) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := checkSetupPrefix state)
  intro i hi
  refine ⟨.base ((checkSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [checkSetupPrefix, checkSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The input gate compares the supplied length with 800 times the opening size. -/
def checkLengthState (state : MachineState) : MachineState :=
  ((checkSetupPrefix state 8).setReg .x7 (state.getReg .x16 * 800)).setPC
    (if state.getReg .x16 * 800 = state.getReg .x17 then 4136 else 4432)

/-- Ten instructions, thirteen cycles, and no queries to reach the length decision. -/
theorem check_length_gate (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (10 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkLengthState state) allowCoins
          return result.charge 13 0) := by
  let ready := checkSetupPrefix state 8
  let multiplied := (ready.setReg .x7 (state.getReg .x16 * 800)).setPC 4132
  have readyPC : ready.pc = 4128 := by
    simp [ready, checkSetupPrefix, checkSetupInstructions, execInstrBr, pc, MachineState.setPC]
  have fetched₁ : fetch (submission.image .check) ready =
      some (.base (.MUL .x7 .x16 .x6)) := by
    apply check_fetch ready 8 _ (by decide) readyPC
    rfl
  have fetched₂ : fetch (submission.image .check) multiplied =
      some (.base (.BNE .x7 .x17 300)) := by
    apply check_fetch multiplied 9 _ (by decide) rfl
    rfl
  have readyCount : ready.getReg .x16 = state.getReg .x16 := by
    simp [ready, checkSetupPrefix, checkSetupInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have readyLength : ready.getReg .x17 = state.getReg .x17 := by
    simp [ready, checkSetupPrefix, checkSetupInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have readyFactor : ready.getReg .x6 = 800 := by
    dsimp only [ready, checkSetupPrefix, checkSetupInstructions, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step₁ : ordinaryStep ready (.base (.MUL .x7 .x16 .x6)) = some multiplied := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      readyCount, readyFactor, readyPC, multiplied]
    rfl
  have step₂ : ordinaryStep multiplied (.base (.BNE .x7 .x17 300)) =
      some (checkLengthState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, multiplied]
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17), readyLength]
    simp [checkLengthState, ready, signExtend13, MachineState.setPC]
    split <;> simp_all
  rw [show 10 + fuel = 8 + (fuel + 2) by omega, check_setup_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched₁ step₁]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched₂ step₂]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- State at HALT, preserving all memory and all registers except the exit controls. -/
def checkExitState (state : MachineState) (success : Bool) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 (if success then 0 else 1)).setPC
    (if success then 4428 else 4440)

/-- Both exit blocks halt in three cycles without consulting the oracle. -/
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

/-- A mismatching length is rejected after thirteen instructions and sixteen cycles. -/
theorem check_wrong_length (state : MachineState) (pc : state.pc = 4096)
    (wrong : state.getReg .x16 * 800 ≠ state.getReg .x17)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (13 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkLengthState state) false, 16, 0⟩ := by
  have rejectPC : (checkLengthState state).pc = 4432 := by
    exact if_neg wrong
  rw [show 13 + fuel = 10 + (3 + fuel) by omega, check_length_gate state pc,
    check_exit _ false rejectPC]
  simp [Execution.charge]

private def checkScratchInstructions : List Instr :=
  [.ADDI .x21 .x0 0, .SLLI .x21 .x21 11, .ADDI .x21 .x21 256]

private def checkScratchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkScratchInstructions.take count).foldl execInstrBr state

/-- Valid lengths proceed to the first position, or accept an empty opening. -/
def checkReadyState (state : MachineState) : MachineState :=
  (checkScratchPrefix state 3).setPC (if state.getReg .x27 = 0 then 4420 else 4152)

private theorem check_scratch_prefix (state : MachineState) (pc : state.pc = 4136)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel
            (checkScratchPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := checkScratchPrefix state)
  intro i hi
  refine ⟨.base ((checkScratchInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (10 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- The four-instruction transition after a valid length, with no memory accesses. -/
theorem check_ready (state : MachineState) (pc : state.pc = 4136)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkReadyState state) allowCoins
          return result.charge 4 0) := by
  let ready := checkScratchPrefix state 3
  have readyPC : ready.pc = 4148 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x27 := by
    simp [ready, checkScratchPrefix, checkScratchInstructions, execInstrBr, signExtend12,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have fetched : fetch (submission.image .check) ready =
      some (.base (.BEQ .x27 .x0 272)) := by
    apply check_fetch ready 13 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 272)) =
      some (checkReadyState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show ready.getReg .x0 = 0 from rfl, readyPC]
    simp [checkReadyState, ready, signExtend13]
    split <;> simp_all
  rw [show 4 + fuel = 3 + (fuel + 1) by omega, check_scratch_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- The length gate preserves the position count and all input memory. -/
theorem check_length_preserves (state : MachineState) :
    (checkLengthState state).getReg .x27 = state.getReg .x16 ∧
    (checkLengthState state).mem = state.mem := by
  dsimp only [checkLengthState, checkSetupPrefix, checkSetupInstructions, List.take, List.foldl,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp

/-- Register mapping after the input gate and scratch initialization. Input
addresses are copied into the outer loop's dedicated registers. -/
theorem check_ready_registers (state : MachineState) :
    (checkReadyState (checkLengthState state)).getReg .x21 = 256 ∧
    (checkReadyState (checkLengthState state)).getReg .x24 = state.getReg .x13 ∧
    (checkReadyState (checkLengthState state)).getReg .x8 = state.getReg .x14 ∧
    (checkReadyState (checkLengthState state)).getReg .x25 = state.getReg .x15 ∧
    (checkReadyState (checkLengthState state)).getReg .x26 = state.getReg .x11 ∧
    (checkReadyState (checkLengthState state)).getReg .x27 = state.getReg .x16 := by
  dsimp only [checkReadyState, checkScratchPrefix, checkScratchInstructions,
    checkLengthState, checkSetupPrefix, checkSetupInstructions, List.take, List.foldl,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp

theorem check_ready_pc (state : MachineState) :
    (checkReadyState (checkLengthState state)).pc =
      if state.getReg .x16 = 0 then 4420 else 4152 := by
  change (if (checkLengthState state).getReg .x27 = 0 then 4420 else 4152) = _
  rw [(check_length_preserves state).1]

/-- Empty openings accept in twenty cycles, without reading data or using the oracle. -/
theorem check_empty_execution (state : MachineState) (pc : state.pc = 4096)
    (count : state.getReg .x16 = 0) (length : state.getReg .x17 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (17 + fuel) state allowCoins =
      pure ⟨.success, checkExitState (checkReadyState (checkLengthState state)) true, 20, 0⟩ := by
  have matched : state.getReg .x16 * 800 = state.getReg .x17 := by rw [count, length]; rfl
  have lengthPC : (checkLengthState state).pc = 4136 := if_pos matched
  have readyPC : (checkReadyState (checkLengthState state)).pc = 4420 :=
    if_pos ((check_length_preserves state).1.trans count)
  rw [show 17 + fuel = 10 + (4 + (3 + fuel)) by omega, check_length_gate state pc,
    check_ready _ lengthPC, check_exit _ true readyPC]
  simp [Execution.charge]

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

/-- The 64-bit length comparison cannot wrap around for any admitted proof. -/
theorem check_input_length (input : CheckInput) (valid : input.proof.length ≤ submission.sizes.proof) :
    ((submission.initialState .check input).getReg .x16 * 800 =
      (submission.initialState .check input).getReg .x17) ↔
      input.proof.length = 800 * input.positions.card := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have countBound : input.positions.card < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have lengthBound : input.proof.length < 2^64 := by
    change input.proof.length ≤ 13421772800 at valid
    norm_num; omega
  have productBound : input.positions.card * 800 < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  change (BitVec.ofNat 64 input.positions.card * 800 = BitVec.ofNat 64 input.proof.length) ↔ _
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound,
    Nat.mod_eq_of_lt lengthBound]
  change (input.positions.card * 800) % 2^64 = input.proof.length ↔ _
  rw [Nat.mod_eq_of_lt productBound]
  omega

/-- Every in-capacity but malformed proof length rejects with exactly sixteen cycles
and zero queries, regardless of the root, values, proof contents, or position set. -/
theorem check_input_wrong_length (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof)
    (wrong : input.proof.length ≠ 800 * input.positions.card) :
    submission.run .check input =
      pure ⟨.failure, checkExitState (checkLengthState (submission.initialState .check input)) false,
        16, 0⟩ := by
  have gateWrong : (submission.initialState .check input).getReg .x16 * 800 ≠
      (submission.initialState .check input).getReg .x17 :=
    fun matched => wrong ((check_input_length input valid).mp matched)
  have steps : submission.steps .check = 13 + (submission.steps .check - 13) := by
    change 214748365824 = 13 + (214748365824 - 13); rfl
  exact (run_check_valid submission input valid).trans
    ((congrArg (fun fuel => execute (submission.image .check) fuel
      (submission.initialState .check input) false) steps).trans
      (check_wrong_length _ rfl gateWrong _ false))

/-- An empty opening with an empty proof succeeds for every commitment and value input. -/
theorem check_input_empty (input : CheckInput) (positions : input.positions = ∅)
    (proof : input.proof = []) :
    submission.run .check input = pure ⟨.success,
      checkExitState (checkReadyState (checkLengthState (submission.initialState .check input))) true,
      20, 0⟩ := by
  have valid : input.proof.length ≤ submission.sizes.proof := by simp [proof]
  have count : (submission.initialState .check input).getReg .x16 = 0 := by
    change BitVec.ofNat 64 input.positions.card = 0
    simp [positions]
  have length : (submission.initialState .check input).getReg .x17 = 0 := by
    change BitVec.ofNat 64 input.proof.length = 0
    simp [proof]
  have steps : submission.steps .check = 17 + (submission.steps .check - 17) := by
    change 214748365824 = 17 + (214748365824 - 17); rfl
  exact (run_check_valid submission input valid).trans
    ((congrArg (fun fuel => execute (submission.image .check) fuel
      (submission.initialState .check input) false) steps).trans
      (check_empty_execution _ rfl count length _ false))

private def checkRootInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x21 (BitVec.ofNat 12 (8 * word)), .LD .x7 .x26 (BitVec.ofNat 12 (8 * word))]

private def checkRootPrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((checkRootInstructions word).take count).foldl execInstrBr state

/-- Compare one of the four 64-bit words of the reconstructed and supplied roots. -/
def checkRootWordState (state : MachineState) (word : Nat) : MachineState :=
  execInstrBr (checkRootPrefix state word 2) (.BNE .x6 .x7 (BitVec.ofNat 13 (64 - 12 * word)))

/-- Each word comparison loads both words and rejects a mismatch before proceeding.
This is an exact three-cycle interpreter transition, not a reference checker. -/
theorem check_root_word (state : MachineState) (word : Nat) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4360 + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkRootWordState state word) allowCoins
          return result.charge 3 0) := by
  have loads (remaining : Nat) : execute (submission.image .check) (2 + remaining) state allowCoins =
      (do let result ← execute (submission.image .check) remaining
            (checkRootPrefix state word 2) allowCoins
          return result.charge 2 0) := by
    apply execute_unit_steps (states := checkRootPrefix state word)
    intro i hi
    refine ⟨.base (((checkRootInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply check_fetch _ (66 + 3 * word + i) _ (by omega)
      · interval_cases word <;> interval_cases i <;>
          simp [checkRootPrefix, checkRootInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases word <;> interval_cases i <;> rfl
    · have offset : signExtend12 (BitVec.ofNat 12 (8 * word)) = BitVec.ofNat 64 (8 * word) := by
        interval_cases word <;> rfl
      interval_cases i <;>
        simp only [checkRootPrefix, checkRootInstructions, List.take, List.foldl,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, offset,
          MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x26)] <;>
        first | rw [scratchValid]; rfl | rw [rootValid]; rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .check) (checkRootPrefix state word 2) =
      some (.base (.BNE .x6 .x7 (BitVec.ofNat 13 (64 - 12 * word)))) := by
    apply check_fetch _ (68 + 3 * word) _ (by omega)
    · interval_cases word <;>
        simp [checkRootPrefix, checkRootInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases word <;> rfl
  have stepped : ordinaryStep (checkRootPrefix state word 2)
      (.base (.BNE .x6 .x7 (BitVec.ofNat 13 (64 - 12 * word)))) =
        some (checkRootWordState state word) := rfl
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, loads]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- A comparison does not alter memory or any non-scratch register. -/
theorem check_root_word_preserves (state : MachineState) (word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordState state word).getReg reg = state.getReg reg ∧
    (checkRootWordState state word).mem = state.mem := by
  constructor
  · simp only [checkRootWordState, checkRootPrefix, checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> simp only [MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLeft),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notRight)]
  · simp only [checkRootWordState, checkRootPrefix, checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> rfl

/-- The branch advances precisely when the two words agree; otherwise it reaches HALT failure. -/
theorem check_root_word_pc (state : MachineState) (word : Nat) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4360 + 12 * word)) :
    (checkRootWordState state word).pc =
      if state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
          state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) then
        BitVec.ofNat 64 (4372 + 12 * word) else 4432 := by
  interval_cases word <;>
    simp [checkRootWordState, checkRootPrefix, checkRootInstructions, execInstrBr,
      signExtend12, signExtend13, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, MachineState.getMem, pc] <;>
    split <;> simp_all

/-- Any mismatching root word produces a failed execution in six cycles and zero queries. -/
theorem check_root_word_reject (state : MachineState) (word : Nat) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4360 + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (6 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkRootWordState state word) false, 6, 0⟩ := by
  have rejectPC : (checkRootWordState state word).pc = 4432 := by
    rw [check_root_word_pc state word bounded pc, if_neg different]
  rw [show 6 + fuel = 3 + (3 + fuel) by omega,
    check_root_word state word bounded pc scratchValid rootValid, check_exit _ false rejectPC]
  simp [Execution.charge]

/-- State after comparing a prefix of the four root words. -/
def checkRootWordsState (state : MachineState) : Nat → MachineState
  | 0 => state
  | count + 1 => checkRootWordState (checkRootWordsState state count) count

theorem check_root_words_preserves (state : MachineState) (count : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordsState state count).getReg reg = state.getReg reg ∧
    (checkRootWordsState state count).mem = state.mem := by
  induction count with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    have preserved := check_root_word_preserves (checkRootWordsState state count) count reg notLeft notRight
    exact ⟨preserved.1.trans ih.1, preserved.2.trans ih.2⟩

private theorem check_root_words_read (state : MachineState) (count word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (checkRootWordsState state count).getMem
        ((checkRootWordsState state count).getReg reg + BitVec.ofNat 64 (8 * word)) =
      state.getMem (state.getReg reg + BitVec.ofNat 64 (8 * word)) := by
  have preserved := check_root_words_preserves state count reg notLeft notRight
  rw [preserved.1]
  exact congrFun preserved.2 _

/-- Matching prefixes proceed through the comparison block in order. -/
theorem check_root_words_pc (state : MachineState) (pc : state.pc = 4360)
    (count : Nat) (bounded : count ≤ 4)
    (agrees : ∀ word < count,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word))) :
    (checkRootWordsState state count).pc = BitVec.ofNat 64 (4360 + 12 * count) := by
  induction count with
  | zero => exact pc
  | succ count ih =>
    have previous := ih (by omega) (fun word bound => agrees word (by omega))
    rw [checkRootWordsState, check_root_word_pc _ count (by omega) previous,
      check_root_words_read state count count .x21 (by decide) (by decide),
      check_root_words_read state count count .x26 (by decide) (by decide),
      if_pos (agrees count (by omega))]
    congr 1
    omega

/-- Execute any matching prefix of the root comparison. This also lets a rejection
proof stop at the first mismatching word. -/
theorem check_root_prefix (state : MachineState) (pc : state.pc = 4360)
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : ∀ word < 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (count : Nat) (bounded : count ≤ 4)
    (agrees : ∀ word < count,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)))
    (remaining : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 * count + remaining) state allowCoins =
      (do let result ← execute (submission.image .check) remaining
            (checkRootWordsState state count) allowCoins
          return result.charge (3 * count) 0) := by
  induction count generalizing remaining with
  | zero => simp [checkRootWordsState, Execution.charge]
  | succ count ih =>
    have position := check_root_words_pc state pc count (by omega)
      (fun word bound => agrees word (by omega))
    have scratch : accessValid ((checkRootWordsState state count).getReg .x21 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(check_root_words_preserves state count .x21 (by decide) (by decide)).1]
      exact scratchValid count (by omega)
    have root : accessValid ((checkRootWordsState state count).getReg .x26 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(check_root_words_preserves state count .x26 (by decide) (by decide)).1]
      exact rootValid count (by omega)
    rw [show 3 * (count + 1) + remaining = 3 * count + (3 + remaining) by omega,
      ih (by omega) (fun word bound => agrees word (by omega)), check_root_word _ count (by omega) position scratch root]
    simp [checkRootWordsState, Execution.charge, Nat.mul_add, ← Nat.add_assoc]

/-- All four matching root words pass in twelve cycles, with no oracle queries.
The memory-validity hypotheses are exactly those checked by the actual loads. -/
theorem check_root_matches (state : MachineState) (pc : state.pc = 4360)
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : ∀ word < 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (agrees : ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (12 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkRootWordsState state 4) allowCoins
          return result.charge 12 0) :=
  check_root_prefix state pc scratchValid rootValid 4 (by decide) agrees fuel allowCoins

private theorem scheme_check_of_run (candidate : Submission) (input : CheckInput)
    (result : Execution) (run : candidate.run .check input = pure result) :
    candidate.scheme.check input.commitment input.positions input.values input.proof =
      pure (result.exit == .success) := by
  change ((fun execution => execution.exit == .success) <$>
    simulateQ checkHandler (candidate.run .check input)) = _
  rw [run]
  simp

/-- Malformed lengths are rejected by the scheme used in the security games, too. -/
theorem check_scheme_wrong_length (input : CheckInput)
    (wrong : input.proof.length ≠ 800 * input.positions.card) :
    submission.scheme.check input.commitment input.positions input.values input.proof = pure false := by
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · exact scheme_check_of_run submission input _ (check_input_wrong_length input valid wrong)
  · exact scheme_check_of_run submission input _ (check_oversized input (by omega))

/-- Empty-opening acceptance also holds for the scheme derived from the image. -/
theorem check_scheme_empty (input : CheckInput) (positions : input.positions = ∅)
    (proof : input.proof = []) :
    submission.scheme.check input.commitment input.positions input.values input.proof = pure true :=
  scheme_check_of_run submission input _ (check_input_empty input positions proof)

/-- Any accepted proof has exactly the required length. This holds against every
fixed oracle, including adversarially chosen roots, values, and proof contents. -/
theorem check_length_of_accept (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (submission.scheme.check input.commitment input.positions
      input.values input.proof)).1 = true) :
    input.proof.length = 800 * input.positions.card := by
  by_contra wrong
  rw [check_scheme_wrong_length input wrong] at accepted
  simp [Oracle.eval] at accepted

private def checkCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def checkCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkCompressionInstructions.take count).foldl execInstrBr state

/-- State after the compression reply overwrites the low half of scratch memory. -/
def checkCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  let ready := checkCompressionPrefix state 5
  writeBits ((savePaddingRegisters (ready.setReg .x31 (ready.pc+4))).setReg .x11 64) 256 answer

/-- Both compression call sites perform precisely one fixed-width oracle query.
Setup costs five cycles and the padded call costs 24. The oracle receives the
64-byte scratch contents followed by 32 zero bytes; every reply is handled by the actual writer. -/
theorem check_compression (state : MachineState) (start : Nat)
    (location : start = 56 ∨ start = 96)
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
    · apply check_fetch _ (start + i) _ (by rcases location with rfl | rfl <;> omega)
      · rcases location with rfl | rfl <;> interval_cases i <;>
          simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := checkCompressionPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (start+5)) := by
    dsimp only [ready]
    rcases location with rfl | rfl <;>
        simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 64 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 := by
    simp [ready, checkCompressionPrefix, checkCompressionInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, scratch]
    rfl
  have call := padding_call true ready (start+5) (by rcases location with rfl | rfl <;> simp [paddingCallSite]) readyPC
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

/-- The padded call returns to the instruction after the five-instruction setup. -/
theorem check_compression_pc (state : MachineState) (answer : BitVec 256) :
    (checkCompressionState state answer).pc = state.pc + 24 := by
  simp [checkCompressionState, writeBits, savePaddingRegisters, checkCompressionPrefix, checkCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

/-- Compression preserves the loop counters, pointers, and return address. The setup overwrites
syscall arguments; the adapter additionally uses x14..x17 and x31. -/
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
/-- Each of the four scratch words receives the corresponding 64 bits of the reply.
This verifies the actual 32 successive byte writes, including little-endian order. -/
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

/-- Compression touches only the four scratch words containing the output digest. -/
theorem check_compression_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkCompressionState state answer).getMem address = state.getMem address := by
  unfold checkCompressionState
  rw [writeBits_memory_outside]
  · rfl
  · intro i hi
    change i < 32 at hi
    interval_cases i <;> norm_num [alignToDword] <;> tauto

private def checkLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56]

private def checkLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkLeafCopyInstructions.take count).foldl execInstrBr state

def checkLeafCopyState (state : MachineState) : MachineState := checkLeafCopyPrefix state 8

private theorem check_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (checkLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [checkLeafCopyPrefix, checkLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

set_option maxHeartbeats 800000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem check_leaf_copy (state : MachineState) (pc : state.pc = 4448)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := checkLeafCopyPrefix state)
  intro i hi
  refine ⟨.base ((checkLeafCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (88 + i) _ (by omega)
    · interval_cases i <;>
        simp [checkLeafCopyPrefix, checkLeafCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := check_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (check_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (checkLeafCopyPrefix state i)
        ((checkLeafCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [checkLeafCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
    interval_cases i <;>
      simp only [checkLeafCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The leaf-loop latch advances to the next block, then decrements the eight-block counter. -/
def checkLeafNextState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 32)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4516 else 4448)

theorem check_leaf_next (state : MachineState) (pc : state.pc = 4504)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafNextState state) allowCoins
          return result.charge 3 0) := by
  let advanced := (state.setReg .x8 (state.getReg .x8 + 32)).setPC 4508
  let next := (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 4512
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x8 .x8 32)) := by
    apply check_fetch _ 102 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply check_fetch _ 103 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) next = some (.base (.BNE .x28 .x0 8128)) := by
    apply check_fetch _ 104 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 32)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep next (.base (.BNE .x28 .x0 8128)) = some (checkLeafNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, checkLeafNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One leaf block: copy 32 bytes, compress, then advance the pointer and counter. -/
def checkLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkLeafNextState (checkCompressionState (checkLeafCopyState state) answer)

theorem check_leaf_block (state : MachineState) (pc : state.pc = 4448)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (33 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer (checkLeafCopyState state) 256 64))))
          let result ← execute (submission.image .check) fuel (checkLeafStepState state answer) allowCoins
          return result.charge 40 1) := by
  have copyPC : (checkLeafCopyState state).pc = 4480 := by
    simp [checkLeafCopyState, checkLeafCopyPrefix, checkLeafCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyScratch : (checkLeafCopyState state).getReg .x21 = 256 :=
    (check_copy_register state 8 (by decide) .x21 (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkCompressionState (checkLeafCopyState state) answer).pc = 4504 := by
    rw [check_compression_pc, copyPC]
    rfl
  rw [show 33 + fuel = 8 + (22 + (3 + fuel)) by omega, check_leaf_copy state pc scratch sourceValid,
    check_compression _ 96 (Or.inr rfl) copyPC copyScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer (checkLeafCopyState state) 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [check_leaf_next _ (compressionPC answer)]
  simp [checkLeafStepState, Execution.charge, ← Nat.add_assoc]

/-- The next iteration has the advanced source pointer and decremented counter;
its scratch pointer and subroutine return address are unchanged. -/
theorem check_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (checkLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (checkLeafStepState state answer).getReg .x28 = state.getReg .x28 - 1 ∧
    (checkLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (checkLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (safe : reg ∈ [Reg.x8, .x28, .x21, .x1]) :
      (checkCompressionState (checkLeafCopyState state) answer).getReg reg = state.getReg reg := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at safe
    rcases safe with rfl | rfl | rfl | rfl <;>
      exact (check_compression_register _ answer _ (by decide) (by decide) (by decide)
        (by decide) (by decide)).trans (check_copy_register state 8 (by decide) _ (by decide))
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
      if state.getReg .x28 - 1 = 0 then 4516 else 4448 := by
  change (if (checkCompressionState (checkLeafCopyState state) answer).getReg .x28 - 1 = 0
    then 4516 else 4448) = _
  rw [check_compression_register _ answer .x28 (by decide) (by decide) (by decide) (by decide) (by decide),
    checkLeafCopyState, check_copy_register state 8 (by decide) .x28 (by decide)]

/-- A semantic unfolding of the actual block loop. Each iteration issues the exact
scratch query from the image and applies its byte-writing and pointer transitions. -/
def checkLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer (checkLeafCopyState state) 256 64))))
      checkLeafLoop (checkLeafStepState state answer) count

/-- Exact execution of the leaf hash loop for every possible sequence of oracle replies.
The loop uses 33 instructions and 40 cycles per block, and makes one query per block. -/
theorem check_leaf_loop (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (pc : 0 < count → state.pc = 4448) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (33 * count + fuel) state allowCoins =
      (do let finished ← checkLeafLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (40 * count) count) := by
  induction count generalizing state with
  | zero => simp [checkLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (checkLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (checkLeafStepState state answer).pc = 4448 := by
      rw [check_leaf_block_pc]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (check_leaf_block_registers state answer).2.1, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((checkLeafStepState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(check_leaf_block_registers state answer).1]
      have address : state.getReg .x8 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 33 * (count + 1) + fuel = 33 + (33 * count + fuel) by omega,
      check_leaf_block state (pc (by omega)) scratch currentValid]
    simp only [checkLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer (checkLeafCopyState state) 256 64))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((check_leaf_block_registers state answer).2.2.1.trans scratch) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every possible run of the bounded loop exhausts its counter and preserves the
return address. A nonempty loop reaches the actual JALR instruction. -/
theorem check_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (checkLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4516) := by
  induction count generalizing state with
  | zero =>
    simp only [checkLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
    simp only [checkLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
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

/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem check_leaf_return (state : MachineState) (pc : state.pc = 4516)
    (link : state.getReg .x1 = 4196) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (state.setPC 4196) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply check_fetch _ 105 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4196) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- The full 2048-bit leaf-hashing subroutine: initialize eight blocks, process them,
and return to the authentication-path code. All oracle replies are covered.
It takes 266 instructions, costs exactly 322 cycles, and makes eight queries. -/
theorem check_leaf_subroutine (state : MachineState) (pc : state.pc = 4444)
    (link : state.getReg .x1 = 4196) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (266 + fuel) state allowCoins =
      (do let finished ← checkLeafLoop ((state.setReg .x28 8).setPC 4448) 8
          let result ← execute (submission.image .check) fuel (finished.setPC 4196) allowCoins
          return result.charge 322 8) := by
  let initialized := (state.setReg .x28 8).setPC 4448
  have fetched : fetch (submission.image .check) state =
      some (.base (.ADDI .x28 .x0 8)) := by
    apply check_fetch _ 87 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.ADDI .x28 .x0 8)) = some initialized := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      initialized, pc, MachineState.getReg]
  have initCounter : initialized.getReg .x28 = BitVec.ofNat 64 8 := by
    simp [initialized, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have initScratch : initialized.getReg .x21 = 256 := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (initialized.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using sourceValid
  rw [show 266 + fuel = (33 * 8 + (1 + fuel)) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped,
    check_leaf_loop initialized 8 (by decide) (fun _ => rfl) initCounter initScratch initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := check_leaf_loop_finished initialized 8 (by decide) initCounter finished reachable
  have finalLink : finished.getReg .x1 = 4196 := by
    rw [done.2.1]
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using link
  rw [check_leaf_return finished (done.2.2 (by decide)) finalLink]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem check_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28, .x14, .x15, .x16, .x17, .x31]) :
    (checkLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28, not14, not15, not16, not17, not31⟩
  simp only [checkLeafStepState, checkLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (check_compression_register _ answer reg not5 not10 not11 not12 not13 not14 not15 not16 not17 not31).trans
    (check_copy_register state 8 (by decide) reg not6)

/-- The complete hash preserves the position/path metadata, proof pointer, root
pointer, and scratch pointer. It consumes exactly 32 bytes per block from x8. -/
theorem check_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (checkLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
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
    have rest := ih _ reached
    constructor
    · rw [rest.1, (check_leaf_block_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (check_leaf_block_preserves state answer reg preserved)

end CommitGolfCandidate
