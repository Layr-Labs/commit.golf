import CommitGolfCandidate.Execution
import CommitGolfCandidate.OpeningNonceCopy

/-! Control-flow proofs for the concrete opening image. Instruction addresses below
are checked against the submitted bytes, rather than a separate assembly model. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem opening_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 60) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
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
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 256,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x18 .x9 .x6]

private def openingSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSetupInstructions.take count).foldl execInstrBr state

private def compactOpeningSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0,.ADDI .x24 .x13 0,.ADDI .x25 .x15 0,.ADDI .x27 .x16 0,
   .LUI .x19 4096,.LUI .x6 262144,.ADD .x18 .x9 .x6,.JAL .x0 48]

private def compactOpeningSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (compactOpeningSetupInstructions.take count).foldl execInstrBr state

private theorem compact_opening_setup_same (state : MachineState) :
    compactOpeningSetupPrefix state 8=openingSetupPrefix state 19 := by
  simp [compactOpeningSetupPrefix,compactOpeningSetupInstructions,openingSetupPrefix,
    openingSetupInstructions,execInstrBr,signExtend21,signExtend12,MachineState.setPC,
    MachineState.setReg,MachineState.getReg,BitVec.add_assoc]
  funext reg
  cases reg <;> rfl

/-- Eight fetched setup instructions produce the former nineteen-instruction state. -/
private theorem opening_setup_prefix (state : MachineState) (pc : state.pc=4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (8+fuel) state allowCoins=
      (do let result ← execute (submission.image .opening) fuel (openingSetupPrefix state 19) allowCoins
          return result.charge 8 0) := by
  rw [← compact_opening_setup_same]
  apply execute_unit_steps (states := compactOpeningSetupPrefix state)
  intro i hi
  refine ⟨.base ((compactOpeningSetupInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply opening_fetch _ i _ (by omega)
    · interval_cases i <;> simp [compactOpeningSetupPrefix,compactOpeningSetupInstructions,
        execInstrBr,pc,MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- State at the first position, or at the return block for an empty opening. -/
def openingInitializedState (state : MachineState) : MachineState :=
  (openingSetupPrefix state 19).setPC
    (if state.getReg .x16 = 0 then 4320 else 4176)

/-- Setup copies the ABI pointers and count, and computes the heap size and salt base.
The original position count and all input memory are preserved. -/
theorem opening_setup_registers (state : MachineState) :
    (openingInitializedState state).getReg .x9 = state.getReg .x12 ∧
    (openingInitializedState state).getReg .x24 = state.getReg .x13 ∧
    (openingInitializedState state).getReg .x25 = state.getReg .x15 ∧
    (openingInitializedState state).getReg .x27 = state.getReg .x16 ∧
    (openingInitializedState state).getReg .x19 = 16777216 ∧
    (openingInitializedState state).getReg .x18 = state.getReg .x12 + 1073741824 ∧
    (openingInitializedState state).getReg .x16 = state.getReg .x16 ∧
    (openingInitializedState state).mem = state.mem := by
  dsimp only [openingInitializedState, openingSetupPrefix, openingSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

/-- Setup preserves the original ABI proof-buffer base. -/
theorem opening_setup_proof_base (state : MachineState) :
    (openingInitializedState state).getReg .x15 = state.getReg .x15 := by
  simp [openingInitializedState, openingSetupPrefix, openingSetupInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- Exact nine-cycle setup from the actual image entry point. -/
theorem opening_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (9 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingInitializedState state) allowCoins
          return result.charge 9 0) := by
  let ready := openingSetupPrefix state 19
  have readyPC : ready.pc = 4172 := by
    simp [ready, openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
  have readyCount : ready.getReg .x27 = state.getReg .x16 := by
    simpa only [openingInitializedState, MachineState.getReg_setPC] using
      (opening_setup_registers state).2.2.2.1
  have fetched : fetch (submission.image .opening) ready =
      some (.base (.BEQ .x27 .x0 148)) := by
    apply opening_fetch ready 19 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep ready (.base (.BEQ .x27 .x0 148)) =
      some (openingInitializedState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show ready.getReg .x0 = 0 from rfl, readyPC]
    simp [openingInitializedState, ready, signExtend13]
    split <;> simp_all
  rw [show 9 + fuel = 8 + (fuel + 1) by omega, opening_setup_prefix state pc]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- The path-loop latch really is a decrement followed by a backward BNE. -/
private theorem opening_fetch_decrement (state : MachineState)
    (pc : state.pc = 4300) :
    fetch (submission.image .opening) state = some (.base (.ADDI .x28 .x28 4095)) := by
  apply opening_fetch state 51 _ (by decide) pc
  rfl

private theorem opening_fetch_branch (state : MachineState)
    (pc : state.pc = 4304) :
    fetch (submission.image .opening) state = some (.base (.BNE .x28 .x0 8136)) := by
  apply opening_fetch state 52 _ (by decide) pc
  rfl

/-- State after the inner loop's two-instruction latch. Counter zero exits to
`open-next`; a nonzero counter branches back to `open-path`. -/
def openingLatchState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x28 - 1
  (state.setReg .x28 remaining).setPC (if remaining = 0 then 4308 else 4248)

/-- Exact interpreter behavior of the loop latch, with arbitrary memory and coins.
The latch costs two cycles and makes no queries. -/
theorem opening_latch (state : MachineState) (pc : state.pc = 4300)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingLatchState state) allowCoins
          return result.charge 2 0) := by
  have first := opening_fetch_decrement state pc
  let next := (state.setReg .x28 (state.getReg .x28 - 1)).setPC 4304
  have second := opening_fetch_branch next rfl
  have step : ordinaryStep state (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have branch : ordinaryStep next (.base (.BNE .x28 .x0 8136)) =
      some (openingLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, openingLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, first, step, second, branch, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- A positive bounded counter strictly decreases at the actual loop latch.
No wraparound is possible for an honest path counter (initially 24). -/
theorem opening_latch_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining) (bounded : remaining ≤ LOG_LENGTH)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    ((openingLatchState state).getReg .x28).toNat = remaining - 1 ∧
    remaining - 1 < remaining := by
  simp only [openingLatchState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0), counter]
  constructor
  · change (BitVec.ofNat 64 remaining - BitVec.ofNat 64 1).toNat = remaining - 1
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) remaining 1 (by decide) (by omega)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    simp only [LOG_LENGTH] at bounded
    omega
  · omega

/-- The outer loop advances the index pointer and decrements the position count. -/
def openingNextState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x27 - 1
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 remaining).setPC
    (if remaining = 0 then 4320 else 4176)

/-- Exact three-instruction transition from `open-next` to the next position or
`open-done`. This also preserves the memory containing the completed proof prefix. -/
theorem opening_next (state : MachineState) (pc : state.pc = 4308)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingNextState state) allowCoins
          return result.charge 3 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x24 .x24 8)) := by
    apply opening_fetch state 53 _ (by decide) pc
    rfl
  let advanced := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4312
  let next := (advanced.setReg .x27 (state.getReg .x27 - 1)).setPC 4316
  have second : fetch (submission.image .opening) advanced =
      some (.base (.ADDI .x27 .x27 4095)) := by
    apply opening_fetch advanced 54 _ (by decide) rfl
    rfl
  have third : fetch (submission.image .opening) next =
      some (.base (.BNE .x27 .x0 8052)) := by
    apply opening_fetch next 55 _ (by decide) rfl
    rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, pc]
  have step₂ : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, next, BitVec.sub_eq_add_neg, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  have step₃ : ordinaryStep next (.base (.BNE .x27 .x0 8052)) =
      some (openingNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, openingNextState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, first, step₁, second, step₂, third, step₃, instructionCycles,
    bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem opening_next_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining) (bounded : remaining ≤ LENGTH)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    ((openingNextState state).getReg .x27).toNat = remaining - 1 ∧
    remaining - 1 < remaining := by
  simp only [openingNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0), counter]
  constructor
  · change (BitVec.ofNat 64 remaining - BitVec.ofNat 64 1).toNat = remaining - 1
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) remaining 1 (by decide) (by omega)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [LENGTH, LOG_LENGTH] at bounded
    omega
  · omega

/-- Final state reports the output cursor's displacement from the ABI proof base. -/
def openingExitState (state : MachineState) : MachineState :=
  (((state.setReg .x11 (state.getReg .x25 - state.getReg .x15)).setReg .x5 1).setReg
    .x10 0).setPC 4332

/-- The actual four-instruction return block costs four cycles and makes no queries. -/
theorem opening_exit (state : MachineState) (pc : state.pc = 4320)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4 + fuel) state allowCoins =
      pure ⟨.success, openingExitState state, 4, 0⟩ := by
  let s₁ := (state.setReg .x11 (state.getReg .x25 - state.getReg .x15)).setPC 4324
  let s₂ := ((state.setReg .x11 (state.getReg .x25 - state.getReg .x15)).setReg
    .x5 1).setPC 4328
  let s₃ := openingExitState state
  have fetch0 : fetch (submission.image .opening) state =
      some (.base (.SUB .x11 .x25 .x15)) := by
    apply opening_fetch state 56 _ (by decide) pc
    rfl
  have fetch1 : fetch (submission.image .opening) s₁ =
      some (.base (.ADDI .x5 .x0 1)) := by
    apply opening_fetch s₁ 57 _ (by decide) rfl
    rfl
  have fetch2 : fetch (submission.image .opening) s₂ =
      some (.base (.ADDI .x10 .x0 0)) := by
    apply opening_fetch s₂ 58 _ (by decide) rfl
    rfl
  have fetch3 : fetch (submission.image .opening) s₃ =
      some (.base .ECALL) := by
    apply opening_fetch s₃ 59 _ (by decide) rfl
    rfl
  have step0 : ordinaryStep state (.base (.SUB .x11 .x25 .x15)) = some s₁ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      s₁, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp [pc]
  have step1 : ordinaryStep s₁ (.base (.ADDI .x5 .x0 1)) = some s₂ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₁, s₂, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have step2 : ordinaryStep s₂ (.base (.ADDI .x10 .x0 0)) = some s₃ := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      s₂, s₃, openingExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  rw [Nat.add_comm 4 fuel]
  simp only [execute, fetch0, step0, fetch1, step1, fetch2, step2, fetch3,
    instructionCycles, bind_assoc, pure_bind]
  dsimp only [s₃, openingExitState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  simp [Execution.charge]

/-- The proved pointer displacement yields exactly 800 bytes per position.
The bound rules out modular overflow, including for a full-vector opening. -/
theorem opening_exit_length (state : MachineState) (positions : Nat)
    (bounded : positions ≤ LENGTH)
    (progress : state.getReg .x25 = state.getReg .x15 + BitVec.ofNat 64 (800 * positions)) :
    ((openingExitState state).getReg .x11).toNat = 800 * positions := by
  change (state.getReg .x25 - state.getReg .x15).toNat = _
  rw [progress, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [LENGTH, LOG_LENGTH] at bounded
  omega

/-- The scored batch's length follows from the same cursor invariant. -/
theorem opening_exit_batch_length (state : MachineState)
    (progress : state.getReg .x25 = state.getReg .x15 + BitVec.ofNat 64 (800 * BATCH)) :
    ((openingExitState state).getReg .x11).toNat = 102400 := by
  have h := opening_exit_length state BATCH (by norm_num [BATCH, LENGTH, LOG_LENGTH]) progress
  simpa [BATCH] using h

/-- For every valid ABI input, the loop starts with exactly the supplied number
of positions. Its natural-number value is bounded by the challenge vector length. -/
theorem opening_entry_count (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ((openingInitializedState (submission.initialState .opening (trapdoor, positions))).getReg
      .x27).toNat = positions.card ∧ positions.card ≤ LENGTH := by
  have bounded : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have counter : (submission.initialState .opening (trapdoor, positions)).getReg .x16 =
      BitVec.ofNat 64 positions.card := rfl
  constructor
  · rw [(opening_setup_registers _).2.2.2.1, counter, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt]
    norm_num [LENGTH, LOG_LENGTH] at bounded
    omega
  · exact bounded

/-- Full result of the empty-opening path, including its actual final machine state. -/
def emptyOpeningResult (trapdoor : BitVec (8 * submission.sizes.trapdoor)) : Execution :=
  ⟨.success, openingExitState (openingInitializedState
    (submission.initialState .opening (trapdoor, ∅))), 13, 0⟩

/-- The complete submitted opening program handles an empty position set in thirteen
cycles, succeeds, and makes no queries, for every serialized trapdoor. -/
theorem opening_empty_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor)) :
    submission.run .opening (trapdoor, ∅) = pure (emptyOpeningResult trapdoor) := by
  let initial := submission.initialState .opening (trapdoor, ∅)
  have pc : initial.pc = 4096 := rfl
  have count : initial.getReg .x16 = 0 := rfl
  have readyPC : (openingInitializedState initial).pc = 4320 := by
    simp [openingInitializedState, MachineState.setPC, count]
  change execute (submission.image .opening) (submission.steps .opening) initial true = _
  have steps : submission.steps .opening = 9 + (4 + (submission.steps .opening - 13)) := by
    norm_num [submission, candidate, LOG_LENGTH, LENGTH]
  rw [steps, opening_setup initial pc, opening_exit _ readyPC]
  simp [emptyOpeningResult, initial, Execution.charge]

/-- The scheme derived from the image produces the empty proof on this path. -/
theorem opening_empty_proof (trapdoor : BitVec (8 * submission.sizes.trapdoor)) :
    submission.scheme.opening trapdoor ∅ = pure [] := by
  let initial := submission.initialState .opening (trapdoor, ∅)
  have initialCount : initial.getReg .x16 = 0 := rfl
  have readyCount : (openingInitializedState initial).getReg .x16 = 0 := by
    rw [(opening_setup_registers initial).2.2.2.2.2.2.1, initialCount]
  have length : ((emptyOpeningResult trapdoor).state.getReg .x11).toNat = 0 := by
    apply opening_exit_length (openingInitializedState initial) 0 (by omega)
    rw [(opening_setup_registers initial).2.2.1]
    simp [openingInitializedState, openingSetupPrefix, openingSetupInstructions,
      execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  change (submission.readProof <$> submission.run .opening (trapdoor, ∅)) = _
  rw [opening_empty_execution]
  have exited : (emptyOpeningResult trapdoor).exit = .success := rfl
  simp [Submission.readProof, Submission.openingSucceeded, length, exited]


/-- Both the salt and sibling copies use these four aligned loads and stores.
Only x6 is scratch; the source (x23), destination (x25), and loop counters survive. -/
private def openingCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16,
   .LD .x6 .x23 24, .SD .x25 .x6 24]

private def openingCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCopyInstructions.take count).foldl execInstrBr state

/-- State after copying one digest. This definition also describes sequential-copy
behavior when buffers overlap; later memory lemmas state the required separation. -/
def openingCopyState (state : MachineState) : MachineState :=
  openingCopyPrefix state 8

/-- Expose the eight decoded copy instructions for memory refinement. -/
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

/-- The digest copy preserves every register except its scratch register. -/
theorem opening_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingCopyState state).getReg reg = state.getReg reg :=
  opening_copy_prefix_register state 8 (by decide) reg scratch

set_option maxHeartbeats 1000000 in
/-- The two copies in the actual image each take eight cycles and make no queries.
All four loads and stores must be in bounds and aligned. -/
theorem opening_copy (state : MachineState) (start : Nat)
    (location : start = 41)
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
  · apply opening_fetch _ (start + i) _ (by rcases location with rfl <;> omega)
    · rcases location with rfl <;> interval_cases i <;>
        simp [openingCopyPrefix, openingCopyInstructions, execInstrBr, pc,
          MachineState.setPC]
    · rcases location with rfl <;> interval_cases i <;> rfl
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


theorem opening_nonce_copy (state : MachineState) (pc : state.pc=4196)
    (sourceValid : ∀ word : Fin 4,accessValid (state.getReg .x23+BitVec.ofNat 64 (8*word.val)) 8=true)
    (destinationValid : ∀ word : Fin 4,accessValid (state.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8=true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (7+fuel) state allowCoins=
      (do let result ← execute (submission.image .opening) fuel (openingNonceCopyState state) allowCoins
          return result.charge 7 0) := by
  have fetched : OpeningNonceFetched (submission.image .opening) := by
    intro current i hi currentPC
    apply opening_fetch current (25+i) _ (by omega)
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using currentPC
    · interval_cases i <;> rfl
  exact opening_nonce_execute _ fetched state pc
    (fun word : Fin 3 => sourceValid ⟨word.val,by omega⟩) destinationValid fuel allowCoins

/-- A 32-byte block inside memory, aligned to eight bytes, admits every load/store
used by the digest copy. The bound also rules out address wraparound. -/
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

/-- Outside the four destination words, copying a digest leaves memory unchanged. -/
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

/-- With disjoint source and destination words, the copy writes all four original
source words to their corresponding destination addresses. -/
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


/-- Copying a digest advances past its eight instructions. -/
theorem opening_copy_pc (state : MachineState) :
    (openingCopyState state).pc = state.pc + 32 := by
  simp [openingCopyState, openingCopyPrefix, openingCopyInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

private def openingPathInstructions : List Instr :=
  [.XORI .x7 .x20 1, .SLLI .x7 .x7 5, .ADD .x23 .x9 .x7]

private def openingPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPathInstructions.take count).foldl execInstrBr state

/-- Compute the sibling's heap address: toggle the low index bit, then multiply by 32. -/
def openingPathPreparedState (state : MachineState) : MachineState :=
  openingPathPrefix state 3

private theorem opening_path_prepare (state : MachineState) (pc : state.pc = 4248)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathPreparedState state) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := openingPathPrefix state)
  intro i hi
  refine ⟨.base ((openingPathInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (38 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPathPrefix, openingPathInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem opening_path_prepare_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x7) (source : reg ≠ .x23) :
    (openingPathPreparedState state).getReg reg = state.getReg reg := by
  dsimp only [openingPathPreparedState, openingPathPrefix, openingPathInstructions,
    List.take, List.foldl, execInstrBr]
  simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source)]

private theorem opening_path_source (state : MachineState) :
    (openingPathPreparedState state).getReg .x23 =
      state.getReg .x9 + ((state.getReg .x20 ^^^ 1) <<< 5) := by
  simp [openingPathPreparedState, openingPathPrefix, openingPathInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC, signExtend12]

/-- Advance the output pointer and move from the current tree node to its parent. -/
def openingPathAdvancedState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x20
    (state.getReg .x20 >>> 1)).setPC 4300

private theorem opening_path_advance (state : MachineState) (pc : state.pc = 4292)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathAdvancedState state) allowCoins
          return result.charge 2 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x25 .x25 32)) := by
    apply opening_fetch state 49 _ (by decide) pc
    rfl
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4296
  have second : fetch (submission.image .opening) next =
      some (.base (.SRLI .x20 .x20 1)) := by
    apply opening_fetch next 50 _ (by decide) rfl
    rfl
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

/-- Exact fifteen-cycle iteration of the submitted opening program. -/
theorem opening_path_iteration (state : MachineState) (pc : state.pc = 4248)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + ((state.getReg .x20 ^^^ 1) <<< 5) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (15 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState state) allowCoins
          return result.charge 15 0) := by
  let ready := openingPathPreparedState state
  let copied := openingCopyState ready
  have readyPC : ready.pc = 4260 := by
    simp [ready, openingPathPreparedState, openingPathPrefix, openingPathInstructions,
      execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4292 := by rw [opening_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 4,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_source]
    exact sourceValid word
  have writes : ∀ word : Fin 4,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_path_prepare_register state .x25 (by decide) (by decide)]
    exact destinationValid word
  rw [show 15 + fuel = 3 + (8 + (2 + (2 + fuel))) by omega,
    opening_path_prepare state pc,
    opening_copy ready 41 rfl readyPC reads writes,
    opening_path_advance copied copiedPC,
    opening_latch (openingPathAdvancedState copied) rfl]
  simp [openingPathState, ready, copied, Execution.charge, ← Nat.add_assoc]

/-- One path iteration preserves the original opening count and advances exactly
one digest in the output and one level in the tree. -/
theorem opening_path_registers (state : MachineState) :
    (openingPathState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (openingPathState state).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (openingPathState state).getReg .x28 = state.getReg .x28 - 1 ∧
    (openingPathState state).getReg .x16 = state.getReg .x16 ∧
    (openingPathState state).getReg .x9 = state.getReg .x9 := by
  simp [openingPathState, openingLatchState, openingPathAdvancedState,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    opening_copy_register, opening_path_prepare_register]


/-- Sibling addresses remain inside the allocated digest heap. The heap has
2^25 slots of 32 bytes (including unused slot zero). -/
theorem opening_sibling_access (heap node : Word)
    (heapBound : heap.toNat + 2 ^ 30 ≤ MEMORY_BYTES)
    (heapAligned : heap.toNat % 8 = 0) (nodeBound : node.toNat < 2 ^ 25)
    (word : Fin 4) :
    accessValid (heap + ((node ^^^ 1) <<< 5) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have siblingBound : node.toNat ^^^ 1 < 2 ^ 25 :=
    Nat.xor_lt_two_pow nodeBound (by decide)
  have offset : ((node ^^^ 1) <<< 5).toNat = (node.toNat ^^^ 1) * 32 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_xor, Nat.shiftLeft_eq]
    change ((node.toNat ^^^ 1) * 32) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt]
    omega
  have total : heap.toNat + (node.toNat ^^^ 1) * 32 < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at heapBound
    omega
  have address : (heap + ((node ^^^ 1) <<< 5)).toNat =
      heap.toNat + (node.toNat ^^^ 1) * 32 := by
    simp only [BitVec.toNat_add, offset, Nat.mod_eq_of_lt total]
  apply opening_digest_access_valid
  · rw [address]
    omega
  · rw [address]
    omega

private theorem copy_pc_setPC (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

private theorem opening_path_pc (state : MachineState) :
    (openingPathState state).pc =
      if state.getReg .x28 - 1 = 0 then 4308 else 4248 := by
  simp [openingPathState, openingLatchState, openingPathAdvancedState,
    copy_pc_setPC, MachineState.getReg_setReg_ne,
    opening_copy_register, opening_path_prepare_register]

/-- The complete sibling loop has a precise linear cost. Its assumptions are
ordinary heap/output bounds and alignment; the memory contents are arbitrary. -/
theorem opening_path_loop (remaining : Nat) (bounded : remaining ≤ LOG_LENGTH)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4248)
    (heapBound : (state.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (nodeBound : (state.getReg .x20).toNat < 2 ^ 25)
    (outputBound : (state.getReg .x25).toNat + 32 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (15 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathState^[remaining] state) allowCoins
          return result.charge (15 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      simp only [LOG_LENGTH] at bounded
      omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPathState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_path_registers state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPathState state).pc = 4248 := by
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
    rw [show 15 * (remaining + 1) + fuel = 15 + (15 * remaining + fuel) by omega,
      opening_path_iteration state (pc (by omega)) reads writes,
      ih (by omega) (openingPathState state) nextCounter nextPC
        (by simpa only [nextHeap] using heapBound)
        (by simpa only [nextHeap] using heapAligned)
        nextNode nextOutputBound nextOutputAligned]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm]


/-- A positive path counter reaches zero and transfers control to `open-next`
after exactly that many iterations. -/
theorem opening_path_finished (remaining : Nat) (positive : 0 < remaining)
    (bounded : remaining ≤ LOG_LENGTH) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (openingPathState^[remaining] state).pc = 4308 ∧
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
      · rw [opening_path_pc, counter, subtract]
        rfl
      · exact nextCounter
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (by omega) (openingPathState state) nextCounter

/-- The original position count, used to calculate the final proof length,
is unchanged by any number of sibling iterations. -/
theorem opening_path_preserves_count (iterations : Nat) (state : MachineState) :
    (openingPathState^[iterations] state).getReg .x16 = state.getReg .x16 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_path_registers _).2.2.2.1, ih]


private def openingPositionInstructions : List Instr :=
  [.LD .x20 .x24 0,.SLLI .x6 .x20 1,.ADD .x6 .x6 .x20,.SLLI .x6 .x6 3,.ADD .x23 .x18 .x6]

private def openingPositionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPositionInstructions.take count).foldl execInstrBr state

/-- Read the next serialized position and compute its salt address. -/
def openingPositionPreparedState (state : MachineState) : MachineState :=
  openingPositionPrefix state 5

private theorem opening_position_prepare (state : MachineState) (pc : state.pc = 4176)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPreparedState state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingPositionPrefix state)
  intro i hi
  refine ⟨.base ((openingPositionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (20 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPositionPrefix, openingPositionInstructions,nonceOffset, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i
    · simpa [openingPositionPrefix, openingPositionInstructions, ordinaryStep,
        memoryArgumentsValid, memAccess, signExtend12] using indexValid
    · rfl
    · rfl
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
      state.getReg .x18 + nonceOffset (state.getMem (state.getReg .x24)) := by
  simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,nonceOffset,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, signExtend12]

private def openingSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 32, .ADD .x20 .x20 .x19, .ADDI .x28 .x0 0,
   .SLLI .x28 .x28 11, .ADDI .x28 .x28 24, .BEQ .x28 .x0 64]

private def openingSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSaltInstructions.take count).foldl execInstrBr state

/-- After the salt copy, advance the proof pointer, enter the leaf's heap slot,
and set the sibling-loop counter to 24. -/
def openingSaltAdvancedState (state : MachineState) : MachineState :=
  openingSaltPrefix state 6

private def compactOpeningSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 32,.ADD .x20 .x20 .x19,.ADDI .x28 .x0 24,.JAL .x0 12]

private def compactOpeningSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (compactOpeningSaltInstructions.take count).foldl execInstrBr state

private theorem compact_opening_salt_same (state : MachineState) :
    compactOpeningSaltPrefix state 4=openingSaltAdvancedState state := by
  simp [compactOpeningSaltPrefix,compactOpeningSaltInstructions,openingSaltAdvancedState,
    openingSaltPrefix,openingSaltInstructions,execInstrBr,signExtend21,signExtend13,signExtend12,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc]
  funext reg
  cases reg <;> rfl

private theorem opening_salt_advance (state : MachineState) (pc : state.pc=4224)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (4+fuel) state allowCoins=
      (do let result ← execute (submission.image .opening) fuel (openingSaltAdvancedState state) allowCoins
          return result.charge 4 0) := by
  rw [← compact_opening_salt_same]
  apply execute_unit_steps (states := compactOpeningSaltPrefix state)
  intro i hi
  refine ⟨.base ((compactOpeningSaltInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · apply opening_fetch _ (32+i) _ (by omega)
    · interval_cases i <;> simp [compactOpeningSaltPrefix,compactOpeningSaltInstructions,
        execInstrBr,pc,MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem opening_salt_register (state : MachineState) (reg : Reg)
    (output : reg ≠ .x25) (index : reg ≠ .x20) (counter : reg ≠ .x28) :
    (openingSaltAdvancedState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [openingSaltAdvancedState, openingSaltPrefix,
    openingSaltInstructions, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, signExtend12]

private theorem opening_salt_advanced (state : MachineState) :
    (openingSaltAdvancedState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (openingSaltAdvancedState state).getReg .x20 = state.getReg .x20 + state.getReg .x19 ∧
    (openingSaltAdvancedState state).getReg .x28 = 24 ∧
    (openingSaltAdvancedState state).pc = state.pc + 24 := by
  simp [openingSaltAdvancedState, openingSaltPrefix, openingSaltInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    signExtend12, BitVec.add_assoc]

/-- State at the sibling-loop entry after copying this position's salt. -/
def openingPositionPathState (state : MachineState) : MachineState :=
  openingSaltAdvancedState (openingNonceCopyState (openingPositionPreparedState state))

/-- The actual position setup and salt copy take fifteen cycles. -/
theorem opening_position_setup (state : MachineState) (pc : state.pc = 4176)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + nonceOffset (state.getMem (state.getReg .x24)) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (16 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPathState state) allowCoins
          return result.charge 16 0) := by
  let ready := openingPositionPreparedState state
  let copied := openingNonceCopyState ready
  have readyPC : ready.pc = 4196 := by
    simp [ready, openingPositionPreparedState, openingPositionPrefix,
      openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4224 := by rw [opening_nonce_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 4,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [(opening_position_prepared state).2]
    exact sourceValid word
  have writes : ∀ word : Fin 4,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 16 + fuel = 5 + (7 + (4 + fuel)) by omega,
    opening_position_prepare state pc indexValid,
    opening_nonce_copy ready readyPC reads writes,
    opening_salt_advance copied copiedPC]
  simp [openingPositionPathState, ready, copied, Execution.charge, ← Nat.add_assoc]


theorem opening_position_path_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (index : reg ≠ .x20) (source : reg ≠ .x23)
    (output : reg ≠ .x25) (counter : reg ≠ .x28) :
    (openingPositionPathState state).getReg reg = state.getReg reg := by
  rw [openingPositionPathState, opening_salt_register _ reg output index counter,
    opening_nonce_copy_register _ reg scratch,
    opening_position_prepare_register _ reg scratch index source]

theorem opening_position_path_registers (state : MachineState) :
    (openingPositionPathState state).getReg .x25 = state.getReg .x25 + 32 ∧
    (openingPositionPathState state).getReg .x20 =
      state.getMem (state.getReg .x24) + state.getReg .x19 ∧
    (openingPositionPathState state).getReg .x28 = 24 := by
  refine ⟨?_, ?_, (opening_salt_advanced _).2.2.1⟩
  · rw [openingPositionPathState, (opening_salt_advanced _).1,
      opening_nonce_copy_register _ .x25 (by decide),
      opening_position_prepare_register _ .x25 (by decide) (by decide) (by decide)]
  · rw [openingPositionPathState, (opening_salt_advanced _).2.1,
      opening_nonce_copy_register _ .x20 (by decide), opening_nonce_copy_register _ .x19 (by decide),
      (opening_position_prepared state).1,
      opening_position_prepare_register _ .x19 (by decide) (by decide) (by decide)]

/-- Salt lookup is safe for every valid vector index, independently of salt contents. -/
theorem opening_salt_access (salts index : Word)
    (saltBound : salts.toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : salts.toNat % 8 = 0) (indexBound : index.toNat < 2 ^ 24)
    (word : Fin 4) :
    accessValid (salts + nonceOffset index + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have offset : (nonceOffset index).toNat = 24*index.toNat := by
    exact nonce_offset_toNat index indexBound
  have total : salts.toNat + 24*index.toNat < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at saltBound
    omega
  have address : (salts + nonceOffset index).toNat = salts.toNat + 24*index.toNat := by
    simp only [BitVec.toNat_add, offset, Nat.mod_eq_of_lt total]
  apply opening_digest_access_valid
  · rw [address]; omega
  · rw [address]; omega

/-- State after one complete salt-plus-path opening and the outer loop latch. -/
def openingPositionState (state : MachineState) : MachineState :=
  openingNextState (openingPathState^[24] (openingPositionPathState state))

/-- One complete position costs 379 cycles and makes no queries, including its
salt, all 24 siblings, and the transition to the next position or return block. -/
theorem opening_position (state : MachineState) (pc : state.pc = 4176)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 800 ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (379 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState state) allowCoins
          return result.charge 379 0) := by
  let path := openingPositionPathState state
  have pathPC : path.pc = 4248 := by
    change (openingPositionPathState state).pc = 4248
    rw [openingPositionPathState, (opening_salt_advanced _).2.2.2, opening_nonce_copy_pc]
    simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
      execInstrBr, pc, MachineState.setPC]
  have pathCounter : path.getReg .x28 = BitVec.ofNat 64 24 :=
    (opening_position_path_registers state).2.2
  have pathHeap : path.getReg .x9 = state.getReg .x9 :=
    opening_position_path_register state .x9 (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat < 2 ^ 25 := by
    rw [(opening_position_path_registers state).2.1, leaves, BitVec.toNat_add]
    change ((state.getMem (state.getReg .x24)).toNat + 16777216) % 2 ^ 64 < 2 ^ 25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 32 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 32) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat + 32 * 24 ≤ MEMORY_BYTES := by
    rw [outputNat]; omega
  have pathAligned : (path.getReg .x25).toNat % 8 = 0 := by rw [outputNat]; omega
  have finishedPC : (openingPathState^[24] path).pc = 4308 :=
    (opening_path_finished 24 (by decide) (by decide) path pathCounter).1
  have reads := opening_salt_access (state.getReg .x18) (state.getMem (state.getReg .x24))
    saltBound saltAligned indexBound
  have writes := opening_digest_access_valid (state.getReg .x25) (by omega) outputAligned
  rw [show 379 + fuel = 16 + (15 * 24 + (3 + fuel)) by omega,
    opening_position_setup state pc indexValid reads writes,
    opening_path_loop 24 (by decide) path pathCounter (fun _ => pathPC)
      (by simpa only [pathHeap] using heapBound)
      (by simpa only [pathHeap] using heapAligned) pathNode pathOutput pathAligned,
    opening_next _ finishedPC]
  simp [openingPositionState, path, Execution.charge, ← Nat.add_assoc]


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
    opening_path_prepare_register _ reg sibling source]

private theorem opening_path_preserves_register (iterations : Nat) (state : MachineState)
    (reg : Reg) (scratch : reg ≠ .x6) (sibling : reg ≠ .x7) (index : reg ≠ .x20)
    (source : reg ≠ .x23) (output : reg ≠ .x25) (counter : reg ≠ .x28) :
    (openingPathState^[iterations] state).getReg reg = state.getReg reg := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply',
      opening_path_register _ reg scratch sibling index source output counter, ih]

/-- The sibling loop emits one 32-byte digest per level. -/
theorem opening_path_output (iterations : Nat) (state : MachineState) :
    (openingPathState^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (32 * iterations) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_path_registers _).1, ih]
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- One position advances the input by eight bytes and the proof by 800 bytes,
while decrementing the number of positions still to open. -/
theorem opening_position_progress (state : MachineState) :
    (openingPositionState state).getReg .x24 = state.getReg .x24 + 8 ∧
    (openingPositionState state).getReg .x25 = state.getReg .x25 + 800 ∧
    (openingPositionState state).getReg .x27 = state.getReg .x27 - 1 ∧
    (openingPositionState state).getReg .x16 = state.getReg .x16 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    opening_path_preserves_register, opening_position_path_register,
    opening_path_output, (opening_position_path_registers state).1, BitVec.add_assoc]

/-- The fixed heap, salt base, and tree size survive a complete position opening. -/
theorem opening_position_bases (state : MachineState) :
    (openingPositionState state).getReg .x9 = state.getReg .x9 ∧
    (openingPositionState state).getReg .x18 = state.getReg .x18 ∧
    (openingPositionState state).getReg .x19 = state.getReg .x19 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState,
    MachineState.getReg_setReg_ne, opening_path_preserves_register,
    opening_position_path_register]

private theorem opening_position_pc (state : MachineState) :
    (openingPositionState state).pc =
      if state.getReg .x27 - 1 = 0 then 4320 else 4176 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState, copy_pc_setPC,
    opening_path_preserves_register, opening_position_path_register]

private theorem opening_copy_memory_below (state : MachineState) (address : Word)
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

private theorem opening_nonce_copy_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 32 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingNonceCopyState state).getMem address = state.getMem address := by
  apply opening_nonce_copy_memory_outside
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
  · simpa only [opening_path_prepare_register state .x25 (by decide) (by decide)] using bounded
  · simpa only [opening_path_prepare_register state .x25 (by decide) (by decide)] using below

/-- Path output never overwrites earlier memory, including the serialized indices. -/
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

/-- A complete salt-and-path opening preserves all memory before its proof output.
This is the separation fact needed to keep subsequent input positions intact. -/
theorem opening_position_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 800 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPositionState state).getMem address = state.getMem address := by
  let path := openingPositionPathState state
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 32 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 32) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at bounded
    omega
  have saltMemory : path.getMem address = state.getMem address := by
    change (openingSaltAdvancedState (openingNonceCopyState
      (openingPositionPreparedState state))).getMem address = _
    have advanceMemory (initial : MachineState) :
        (openingSaltAdvancedState initial).getMem address = initial.getMem address := by
      simp [openingSaltAdvancedState, openingSaltPrefix, openingSaltInstructions,
        execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
        MachineState.getMem, signExtend12]
    rw [advanceMemory, opening_nonce_copy_memory_below]
    · simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions, execInstrBr]
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)]
        using (show (state.getReg .x25).toNat + 32 ≤ MEMORY_BYTES by omega)
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)] using below
  simp only [openingPositionState, openingNextState, MachineState.getMem_setPC, MachineState.getMem_setReg]
  rw [opening_path_loop_memory_below 24 path address, saltMemory]
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
/-- Execute all remaining positions. The index buffer precedes the proof buffer,
so every iteration preserves the indices that later iterations will read. -/
theorem opening_positions_loop (remaining : Nat) (bounded : remaining ≤ LENGTH)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4176)
    (indices : ∀ offset < remaining,
      (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24)
    (indexSpace : (state.getReg .x24).toNat + 8 * remaining ≤ (state.getReg .x25).toNat)
    (indexAligned : (state.getReg .x24).toNat % 8 = 0)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 2 ^ 30 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 800 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (379 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState^[remaining] state) allowCoins
          return result.charge (379 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by
      norm_num [LENGTH, LOG_LENGTH] at bounded
      omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPositionState state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [(opening_position_progress state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPositionState state).pc = 4176 := by
      intro positive
      rw [opening_position_pc, counter, subtract, if_neg]
      intro zero
      have equal := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at equal
      rw [Nat.mod_eq_of_lt small] at equal
      omega
    have nextIndex : ((openingPositionState state).getReg .x24).toNat =
        (state.getReg .x24).toNat + 8 := by
      rw [(opening_position_progress state).1]
      exact opening_address_add (state.getReg .x24) 8 (by omega)
    have nextOutput : ((openingPositionState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 800 := by
      rw [(opening_position_progress state).2.1]
      exact opening_address_add (state.getReg .x25) 800 (by omega)
    have nextIndices : ∀ offset < remaining,
        ((openingPositionState state).getMem
          ((openingPositionState state).getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
      intro offset offsetBound
      have address : (openingPositionState state).getReg .x24 + BitVec.ofNat 64 (8 * offset) =
          state.getReg .x24 + BitVec.ofNat 64 (8 * (offset + 1)) := by
        rw [(opening_position_progress state).1]
        simp only [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]
        rw [BitVec.add_comm (8 : Word)]
        rfl
      rw [address, opening_position_memory_below]
      · exact indices (offset + 1) (by omega)
      · omega
      · rw [opening_address_add _ _ (by omega)]
        omega
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simp only [accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, indexAligned⟩
    have indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using indices 0 (by omega)
    have nextBases := opening_position_bases state
    rw [show 379 * (remaining + 1) + fuel = 379 + (379 * remaining + fuel) by omega,
      opening_position state (pc (by omega)) indexValid indexBound leaves
        saltBound saltAligned heapBound heapAligned (by omega) outputAligned,
      ih (by omega) (openingPositionState state) nextCounter nextPC nextIndices
        (by rw [nextIndex, nextOutput]; omega) (by rw [nextIndex]; omega)
        (by simpa only [nextBases.2.2] using leaves)
        (by simpa only [nextBases.2.1] using saltBound)
        (by simpa only [nextBases.2.1] using saltAligned)
        (by simpa only [nextBases.1] using heapBound)
        (by simpa only [nextBases.1] using heapAligned)
        (by rw [nextOutput]; omega) (by rw [nextOutput]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

/-- The complete position loop reaches the return block with its counter at zero. -/
theorem opening_positions_finished (remaining : Nat) (positive : 0 < remaining)
    (state : MachineState) (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (openingPositionState^[remaining] state).pc = 4320 ∧
    (openingPositionState^[remaining] state).getReg .x27 = 0 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPositionState state).getReg .x27 = BitVec.ofNat 64 remaining := by
      rw [(opening_position_progress state).2.2.1, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      constructor
      · rw [opening_position_pc, counter, subtract]; rfl
      · exact nextCounter
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (openingPositionState state) nextCounter

/-- Preserve the original ABI opening count throughout the outer loop. -/
theorem opening_positions_preserves_count (iterations : Nat) (state : MachineState) :
    (openingPositionState^[iterations] state).getReg .x16 = state.getReg .x16 := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_position_progress _).2.2.2, ih]


/-- The outer loop never changes the original ABI proof-buffer base. -/
theorem opening_positions_preserves_proof_base (iterations : Nat) (state : MachineState) :
    (openingPositionState^[iterations] state).getReg .x15 = state.getReg .x15 := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [-Function.iterate_succ, openingPositionState, openingNextState,
      MachineState.getReg_setReg_ne, opening_path_preserves_register,
      opening_position_path_register]

/-- Each completed position appends its salt and 24 sibling digests. -/
theorem opening_positions_output (iterations : Nat) (state : MachineState) :
    (openingPositionState^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (800 * iterations) := by
  induction iterations generalizing state with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply, ih, (opening_position_progress state).2.1]
    simp only [Nat.mul_succ, BitVec.ofNat_add]
    rw [BitVec.add_assoc, BitVec.add_comm (800 : Word) (BitVec.ofNat 64 (800 * iterations))]
    rfl

end CommitGolfCandidate
