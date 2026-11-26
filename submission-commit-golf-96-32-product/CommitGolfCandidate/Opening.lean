import CommitGolfCandidate.Execution
import CommitGolfCandidate.HeapLayout

/-! Control-flow proofs for the concrete opening image. Instruction addresses below
are checked against the submitted bytes, rather than a separate assembly model. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem opening_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 96) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
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


/-- The path-loop latch really is a decrement followed by a backward BNE. -/
private theorem opening_fetch_decrement (state : MachineState)
    (pc : state.pc = 4420) :
    fetch (submission.image .opening) state = some (.base (.ADDI .x28 .x28 4095)) := by
  apply opening_fetch state 81 _ (by decide) pc
  rfl

private theorem opening_fetch_branch (state : MachineState)
    (pc : state.pc = 4424) :
    fetch (submission.image .opening) state = some (.base (.BNE .x28 .x0 8128)) := by
  apply opening_fetch state 82 _ (by decide) pc
  rfl

/-- State after the inner loop's two-instruction latch. Counter zero exits to
`open-next`; a nonzero counter branches back to `open-path`. -/
def openingLatchState (state : MachineState) : MachineState :=
  let remaining := state.getReg .x28 - 1
  (state.setReg .x28 remaining).setPC (if remaining = 0 then 4428 else 4360)

/-- Exact interpreter behavior of the loop latch, with arbitrary memory and coins.
The latch costs two cycles and makes no queries. -/
theorem opening_latch (state : MachineState) (pc : state.pc = 4420)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingLatchState state) allowCoins
          return result.charge 2 0) := by
  have first := opening_fetch_decrement state pc
  let next := (state.setReg .x28 (state.getReg .x28 - 1)).setPC 4424
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

/-- A positive bounded counter strictly decreases at the actual loop latch.
No wraparound is possible for an honest path counter (initially 17). -/
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
    (if remaining = 0 then 4440 else 4292)

/-- Exact three-instruction transition from `open-next` to the next position or
`open-done`. This also preserves the memory containing the completed proof prefix. -/
theorem opening_next (state : MachineState) (pc : state.pc = 4428)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingNextState state) allowCoins
          return result.charge 3 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x24 .x24 8)) := by
    apply opening_fetch state 83 _ (by decide) pc
    rfl
  let advanced := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4432
  let next := (advanced.setReg .x27 (state.getReg .x27 - 1)).setPC 4436
  have second : fetch (submission.image .opening) advanced =
      some (.base (.ADDI .x27 .x27 4095)) := by
    apply opening_fetch advanced 84 _ (by decide) rfl
    rfl
  have third : fetch (submission.image .opening) next =
      some (.base (.BNE .x27 .x0 8048)) := by
    apply opening_fetch next 85 _ (by decide) rfl
    rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, pc]
  have step₂ : ordinaryStep advanced (.base (.ADDI .x27 .x27 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      advanced, next, BitVec.sub_eq_add_neg, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  have step₃ : ordinaryStep next (.base (.BNE .x27 .x0 8048)) =
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


/-- The return block: `x6 = 568`, `x11 = x16 * 568 + 4096` (cap plus records), then the
success request. The final ECALL halts. -/
private def openingExitInstructions : List Instr :=
  [.ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 568, .MUL .x11 .x16 .x6,
   .ADDI .x11 .x11 2047, .ADDI .x11 .x11 2047, .ADDI .x11 .x11 2,
   .ADDI .x5 .x0 1, .ADDI .x10 .x0 0]

private def openingExitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingExitInstructions.take count).foldl execInstrBr state

/-- Final machine state after reporting the opening length and requesting success. -/
def openingExitState (state : MachineState) : MachineState :=
  openingExitPrefix state 9

private theorem opening_exit_prefix_pc (state : MachineState) (pc : state.pc = 4440)
    (count : Nat) (bounded : count ≤ 9) :
    (openingExitPrefix state count).pc = BitVec.ofNat 64 (4096 + 4 * (86 + count)) := by
  interval_cases count <;>
    simp [openingExitPrefix, openingExitInstructions, execInstrBr, pc, MachineState.setPC]

theorem opening_exit_memory (state : MachineState) :
    (openingExitState state).mem = state.mem := by
  simp [openingExitState, openingExitPrefix, openingExitInstructions, execInstrBr,
    MachineState.setReg, MachineState.setPC]

theorem opening_exit_registers (state : MachineState) :
    (openingExitState state).getReg .x11 = state.getReg .x16 * 568 + 4096 ∧
    (openingExitState state).getReg .x5 = 1 ∧
    (openingExitState state).getReg .x10 = 0 := by
  have zero : state.getReg .x0 = 0 := rfl
  simp [zero, openingExitState, openingExitPrefix, openingExitInstructions, execInstrBr,
    MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, signExtend12,
    BitVec.add_assoc]

/-- The actual return block halts successfully and costs exactly thirteen cycles
(including the four-cycle multiplication), with no queries. -/
theorem opening_exit (state : MachineState) (pc : state.pc = 4440)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (10 + fuel) state allowCoins =
      pure ⟨.success, openingExitState state, 13, 0⟩ := by
  have unit₁ (more : Nat) : execute (submission.image .opening) (3 + more) state allowCoins =
      (do let result ← execute (submission.image .opening) more
            (openingExitPrefix state 3) allowCoins
          return result.charge 3 0) := by
    apply execute_unit_steps (states := openingExitPrefix state)
    intro i hi
    refine ⟨.base ((openingExitInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply opening_fetch _ (86 + i) _ (by omega) (opening_exit_prefix_pc state pc i (by omega))
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have multiplyFetch : fetch (submission.image .opening) (openingExitPrefix state 3) =
      some (.base (.MUL .x11 .x16 .x6)) := by
    apply opening_fetch _ 89 _ (by decide) (opening_exit_prefix_pc state pc 3 (by decide))
    rfl
  have multiplyStep : ordinaryStep (openingExitPrefix state 3) (.base (.MUL .x11 .x16 .x6)) =
      some (openingExitPrefix state 4) := rfl
  have unit₂ (more : Nat) : execute (submission.image .opening) (5 + more)
      (openingExitPrefix state 4) allowCoins =
      (do let result ← execute (submission.image .opening) more
            (openingExitPrefix state 9) allowCoins
          return result.charge 5 0) := by
    change execute _ (5 + more) ((fun i => openingExitPrefix state (4 + i)) 0) allowCoins =
      (do let result ← execute _ more ((fun i => openingExitPrefix state (4 + i)) 5) allowCoins
          return result.charge 5 0)
    apply execute_unit_steps (states := fun i => openingExitPrefix state (4 + i))
    intro i hi
    refine ⟨.base ((openingExitInstructions[4 + i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply opening_fetch _ (86 + (4 + i)) _ (by omega)
        (opening_exit_prefix_pc state pc (4 + i) (by omega))
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have haltFetch : fetch (submission.image .opening) (openingExitState state) =
      some (.base .ECALL) := by
    apply opening_fetch _ 95 _ (by decide) (opening_exit_prefix_pc state pc 9 (by decide))
    rfl
  have registers := opening_exit_registers state
  have halt (more : Nat) : execute (submission.image .opening) (more + 1)
      (openingExitPrefix state 9) allowCoins = pure ⟨.success, openingExitState state, 1, 0⟩ := by
    change execute _ (more + 1) (openingExitState state) allowCoins = _
    simp only [execute, haltFetch, registers.2.1, registers.2.2]
    simp
  rw [show 10 + fuel = 3 + ((5 + (fuel + 1)) + 1) by omega, unit₁,
    execute_ordinary_step _ _ _ _ _ _ multiplyFetch multiplyStep, unit₂, halt]
  simp [Execution.charge, instructionCycles]

/-- Reporting the proof length cannot overflow a 64-bit register, even when all
positions are opened. In particular, the scored 128-position opening reports 76800. -/
theorem opening_exit_length (state : MachineState) (positions : Nat)
    (bounded : positions ≤ LENGTH)
    (count : state.getReg .x16 = BitVec.ofNat 64 positions) :
    ((openingExitState state).getReg .x11).toNat = 4096 + 568 * positions := by
  rw [(opening_exit_registers state).1, count]
  norm_num [LENGTH, LOG_LENGTH] at bounded
  have value : BitVec.ofNat 64 positions * 568 + 4096 =
      BitVec.ofNat 64 (4096 + 568 * positions) := by
    rw [show (568 : Word) = BitVec.ofNat 64 568 from rfl,
      show (4096 : Word) = BitVec.ofNat 64 4096 from rfl, ← BitVec.ofNat_mul,
      ← BitVec.ofNat_add]
    congr 1
    omega
  rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]


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
    (location : start = 71)
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


/-! ### Setup and cap emission

Setup copies the ABI pointers and count, computes the tree size, the salt base and the
cap source `x23 = heap + 96*64`, and loads the cap counter `x28 = 64`. Each of the 64
cap iterations copies the 64-byte heap pair `(128+2k, 128+2k+1)` (at heap offset
`6144 + 96k`) to proof offset `64k`, so cap node `m` lands at proof offset `32m`. -/

/-- The twenty-eight straight-line setup instructions before the cap loop. -/
private def openingSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0, .ADDI .x24 .x13 0, .ADDI .x25 .x15 0, .ADDI .x27 .x16 0,
   .ADDI .x19 .x0 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 4,
   .SLLI .x19 .x19 11, .ADDI .x19 .x19 0, .SLLI .x19 .x19 11, .ADDI .x19 .x19 0,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 384,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 0,
   .ADD .x18 .x9 .x6,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 3,
   .SLLI .x6 .x6 11, .ADDI .x6 .x6 0, .ADD .x23 .x9 .x6,
   .ADDI .x28 .x0 0, .SLLI .x28 .x28 11, .ADDI .x28 .x28 64]

private def openingSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSetupInstructions.take count).foldl execInstrBr state

/-- State entering the cap loop. -/
def openingCapStartState (state : MachineState) : MachineState :=
  openingSetupPrefix state 28

/-- Execution of setup is checked against every corresponding instruction encoding. -/
private theorem opening_setup_prefix (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (28 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapStartState state) allowCoins
          return result.charge 28 0) := by
  apply execute_unit_steps (states := openingSetupPrefix state)
  intro i hi
  refine ⟨.base ((openingSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [openingSetupPrefix, openingSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem opening_cap_start_registers (state : MachineState) :
    (openingCapStartState state).getReg .x9 = state.getReg .x12 ∧
    (openingCapStartState state).getReg .x24 = state.getReg .x13 ∧
    (openingCapStartState state).getReg .x25 = state.getReg .x15 ∧
    (openingCapStartState state).getReg .x27 = state.getReg .x16 ∧
    (openingCapStartState state).getReg .x19 = 16777216 ∧
    (openingCapStartState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (openingCapStartState state).getReg .x16 = state.getReg .x16 ∧
    (openingCapStartState state).getReg .x23 = state.getReg .x12 + 6144 ∧
    (openingCapStartState state).getReg .x28 = 64 ∧
    (openingCapStartState state).mem = state.mem := by
  dsimp only [openingCapStartState, openingSetupPrefix, openingSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp

theorem opening_cap_start_pc (state : MachineState) (pc : state.pc = 4096) :
    (openingCapStartState state).pc = 4208 := by
  simp [openingCapStartState, openingSetupPrefix, openingSetupInstructions, execInstrBr,
    pc, MachineState.setPC]

/-- The cap loop body: copy 64 bytes, advance source by 96 and output by 64, decrement. -/
private def openingCapInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0, .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16, .LD .x6 .x23 24, .SD .x25 .x6 24,
   .LD .x6 .x23 32, .SD .x25 .x6 32, .LD .x6 .x23 40, .SD .x25 .x6 40,
   .LD .x6 .x23 48, .SD .x25 .x6 48, .LD .x6 .x23 56, .SD .x25 .x6 56,
   .ADDI .x23 .x23 96, .ADDI .x25 .x25 64, .ADDI .x28 .x28 4095]

private def openingCapPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingCapInstructions.take count).foldl execInstrBr state

private def openingCapAdvance (state : MachineState) : MachineState :=
  ([.ADDI .x23 .x23 96, .ADDI .x25 .x25 64, .ADDI .x28 .x28 4095] : List Instr).foldl
    execInstrBr state

private theorem opening_cap_prefix_split (state : MachineState) :
    openingCapPrefix state 19 = openingCapAdvance (openingCapPrefix state 16) := rfl

/-- One complete cap iteration, including the backward branch. -/
def openingCapState (state : MachineState) : MachineState :=
  (openingCapPrefix state 19).setPC
    (if (openingCapPrefix state 19).getReg .x28 = 0 then 4288 else 4208)

private theorem opening_cap_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 16) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingCapPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [openingCapPrefix, openingCapInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, copy_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

private theorem opening_cap_prefix_pc (state : MachineState) (pc : state.pc = 4208)
    (count : Nat) (bounded : count ≤ 19) :
    (openingCapPrefix state count).pc = BitVec.ofNat 64 (4096 + 4 * (28 + count)) := by
  interval_cases count <;>
    simp [openingCapPrefix, openingCapInstructions, execInstrBr, pc, MachineState.setPC]

private theorem opening_cap_branch (state : MachineState) (pc : state.pc = 4284) :
    ordinaryStep state (.base (.BNE .x28 .x0 8116)) =
      some (state.setPC (if state.getReg .x28 = 0 then 4288 else 4208)) := by
  simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, pc,
    MachineState.getReg, MachineState.setPC]
  split <;> simp_all

/-- An aligned 64-byte block inside memory admits all eight word accesses. -/
theorem opening_pair_access_valid (address : Word)
    (bounded : address.toNat + 64 ≤ MEMORY_BYTES)
    (aligned : address.toNat % 8 = 0) (word : Fin 8) :
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

set_option maxHeartbeats 4000000 in
/-- Exact twenty-cycle cap iteration of the submitted opening program. -/
theorem opening_cap_iteration (state : MachineState) (pc : state.pc = 4208)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 8,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (20 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapState state) allowCoins
          return result.charge 20 0) := by
  have straight : execute (submission.image .opening) (19 + (fuel + 1)) state allowCoins =
      (do let result ← execute (submission.image .opening) (fuel + 1)
            (openingCapPrefix state 19) allowCoins
          return result.charge 19 0) := by
    apply execute_unit_steps (states := openingCapPrefix state)
    intro i hi
    refine ⟨.base ((openingCapInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply opening_fetch _ (28 + i) _ (by omega) (opening_cap_prefix_pc state pc i (by omega))
      interval_cases i <;> rfl
    · by_cases memory : i < 16
      · have s0 := sourceValid ⟨0, by decide⟩
        have s1 := sourceValid ⟨1, by decide⟩
        have s2 := sourceValid ⟨2, by decide⟩
        have s3 := sourceValid ⟨3, by decide⟩
        have s4 := sourceValid ⟨4, by decide⟩
        have s5 := sourceValid ⟨5, by decide⟩
        have s6 := sourceValid ⟨6, by decide⟩
        have s7 := sourceValid ⟨7, by decide⟩
        have d0 := destinationValid ⟨0, by decide⟩
        have d1 := destinationValid ⟨1, by decide⟩
        have d2 := destinationValid ⟨2, by decide⟩
        have d3 := destinationValid ⟨3, by decide⟩
        have d4 := destinationValid ⟨4, by decide⟩
        have d5 := destinationValid ⟨5, by decide⟩
        have d6 := destinationValid ⟨6, by decide⟩
        have d7 := destinationValid ⟨7, by decide⟩
        have sourceReg := opening_cap_prefix_register state i (by omega) .x23 (by decide)
        have destinationReg := opening_cap_prefix_register state i (by omega) .x25 (by decide)
        have valid : memoryArgumentsValid (openingCapPrefix state i)
            ((openingCapInstructions[i]?).getD .EBREAK) = true := by
          interval_cases i <;>
            simp only [openingCapInstructions, List.getElem?_cons_zero,
              List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
              sourceReg, destinationReg, signExtend12] <;>
            first | exact s0 | exact s1 | exact s2 | exact s3 | exact s4 | exact s5 |
              exact s6 | exact s7 | exact d0 | exact d1 | exact d2 | exact d3 |
              exact d4 | exact d5 | exact d6 | exact d7
        interval_cases i <;>
          simp only [openingCapInstructions, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
          simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have branchPC : (openingCapPrefix state 19).pc = 4284 := by
    rw [opening_cap_prefix_pc state pc 19 (by decide)]
    rfl
  have branchFetch : fetch (submission.image .opening) (openingCapPrefix state 19) =
      some (.base (.BNE .x28 .x0 8116)) := by
    apply opening_fetch _ 47 _ (by decide) (opening_cap_prefix_pc state pc 19 (by decide))
    rfl
  rw [show 20 + fuel = 19 + (fuel + 1) by omega, straight,
    execute_ordinary_step _ _ _ _ _ _ branchFetch (opening_cap_branch _ branchPC)]
  simp [openingCapState, instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- A cap iteration advances both pointers and decrements the counter. -/
theorem opening_cap_registers (state : MachineState) :
    (openingCapState state).getReg .x23 = state.getReg .x23 + 96 ∧
    (openingCapState state).getReg .x25 = state.getReg .x25 + 64 ∧
    (openingCapState state).getReg .x28 = state.getReg .x28 - 1 := by
  have x23 := opening_cap_prefix_register state 16 (by decide) .x23 (by decide)
  have x25 := opening_cap_prefix_register state 16 (by decide) .x25 (by decide)
  have x28 := opening_cap_prefix_register state 16 (by decide) .x28 (by decide)
  simp only [openingCapState, MachineState.getReg_setPC, opening_cap_prefix_split]
  simp [openingCapAdvance, execInstrBr, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq, signExtend12, x23, x25, x28, BitVec.sub_eq_add_neg]

/-- A cap iteration preserves every register except its scratch, pointers and counter. -/
theorem opening_cap_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (source : reg ≠ .x23) (output : reg ≠ .x25)
    (counter : reg ≠ .x28) :
    (openingCapState state).getReg reg = state.getReg reg := by
  have kept := opening_cap_prefix_register state 16 (by decide) reg scratch
  simp only [openingCapState, MachineState.getReg_setPC, opening_cap_prefix_split]
  simp only [openingCapAdvance, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm output),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm counter), kept]

private theorem opening_cap_mem (state : MachineState) :
    (openingCapState state).mem = (openingCapPrefix state 16).mem := by
  simp only [openingCapState, opening_cap_prefix_split]
  simp [openingCapAdvance, execInstrBr, MachineState.setReg, MachineState.setPC]

private theorem opening_cap_getMem (state : MachineState) (address : Word) :
    (openingCapState state).getMem address = (openingCapPrefix state 16).getMem address := by
  simp only [MachineState.getMem, opening_cap_mem]

private theorem cap_copy_word (state : MachineState) (offset : BitVec 12) (address : Word) :
    (execInstrBr (execInstrBr state (.LD .x6 .x23 offset)) (.SD .x25 .x6 offset)).getMem address =
      if address = state.getReg .x25 + signExtend12 offset then
        state.getMem (state.getReg .x23 + signExtend12 offset)
      else state.getMem address := by
  simp [execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    copy_getReg_setMem, copy_getMem_setMem]

private theorem cap_offset (k : Nat) (bounded : k < 8) :
    signExtend12 (BitVec.ofNat 12 (8 * k)) = BitVec.ofNat 64 (8 * k) := by
  interval_cases k <;> rfl

private theorem cap_prefix_pair (state : MachineState) (k : Nat) (bounded : k < 8) :
    openingCapPrefix state (2 * k + 2) =
      execInstrBr (execInstrBr (openingCapPrefix state (2 * k))
        (.LD .x6 .x23 (BitVec.ofNat 12 (8 * k)))) (.SD .x25 .x6 (BitVec.ofNat 12 (8 * k))) := by
  interval_cases k <;> rfl

/-- One load/store pair of the cap copy, in terms of the iteration's initial pointers. -/
private theorem cap_pair_getMem (state : MachineState) (k : Nat) (bounded : k < 8)
    (address : Word) :
    (openingCapPrefix state (2 * k + 2)).getMem address =
      if address = state.getReg .x25 + BitVec.ofNat 64 (8 * k) then
        (openingCapPrefix state (2 * k)).getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * k))
      else (openingCapPrefix state (2 * k)).getMem address := by
  rw [cap_prefix_pair state k bounded, cap_copy_word, cap_offset k bounded,
    opening_cap_prefix_register state (2 * k) (by omega) .x25 (by decide),
    opening_cap_prefix_register state (2 * k) (by omega) .x23 (by decide)]

private theorem word_offset_ne (base : Word) (i j : Nat) (iBound : i < 8) (jBound : j < 8)
    (different : i ≠ j) :
    base + BitVec.ofNat 64 (8 * i) ≠ base + BitVec.ofNat 64 (8 * j) := by
  intro equal
  have natural := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp equal)
  simp only [BitVec.toNat_ofNat] at natural
  rw [Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 8 * j < 2 ^ 64)] at natural
  omega

private theorem cap_prefix_outside (state : MachineState) (address : Word)
    (outside : ∀ word < 8, address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word)) :
    ∀ pairs ≤ 8, (openingCapPrefix state (2 * pairs)).getMem address = state.getMem address := by
  intro pairs
  induction pairs with
  | zero => intro _; rfl
  | succ pairs ih =>
    intro bounded
    rw [show 2 * (pairs + 1) = 2 * pairs + 2 by omega, cap_pair_getMem state pairs (by omega),
      if_neg (outside pairs (by omega)), ih (by omega)]

private theorem cap_prefix_written (state : MachineState) (word : Nat) (wordBound : word < 8) :
    ∀ pairs ≤ 8, word < pairs →
      (openingCapPrefix state (2 * pairs)).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) =
        (openingCapPrefix state (2 * word + 2)).getMem
          (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) := by
  intro pairs
  induction pairs with
  | zero => intro _ inside; omega
  | succ pairs ih =>
    intro bounded inside
    by_cases same : word = pairs
    · subst same; rfl
    · rw [show 2 * (pairs + 1) = 2 * pairs + 2 by omega, cap_pair_getMem state pairs (by omega),
        if_neg (word_offset_ne _ word pairs wordBound (by omega) same), ih (by omega) (by omega)]

private theorem cap_prefix_source (state : MachineState) (word : Nat) (wordBound : word < 8)
    (separated : ∀ destination < 8, state.getReg .x23 + BitVec.ofNat 64 (8 * word) ≠
      state.getReg .x25 + BitVec.ofNat 64 (8 * destination)) :
    ∀ pairs ≤ 8, (openingCapPrefix state (2 * pairs)).getMem
        (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) := by
  intro pairs
  induction pairs with
  | zero => intro _; rfl
  | succ pairs ih =>
    intro bounded
    rw [show 2 * (pairs + 1) = 2 * pairs + 2 by omega, cap_pair_getMem state pairs (by omega),
      if_neg (separated pairs (by omega)), ih (by omega)]

/-- Outside the eight destination words, a cap iteration leaves memory unchanged. -/
theorem opening_cap_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 8,
      address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) :
    (openingCapState state).getMem address = state.getMem address := by
  rw [opening_cap_getMem]
  exact cap_prefix_outside state address (fun word inside => outside ⟨word, inside⟩) 8 le_rfl

/-- With disjoint source and destination words, a cap iteration writes all eight
original source words to the corresponding destination words. -/
theorem opening_cap_memory (state : MachineState)
    (separated : ∀ source destination : Fin 8,
      state.getReg .x23 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x25 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 8) :
    (openingCapState state).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  rw [opening_cap_getMem]
  have written := cap_prefix_written state word.val word.isLt 8 le_rfl word.isLt
  rw [show (2 * 8 : Nat) = 16 from rfl] at written
  rw [written, cap_pair_getMem state word.val word.isLt, if_pos rfl]
  exact cap_prefix_source state word.val word.isLt
    (fun destination inside => separated word ⟨destination, inside⟩) word.val (by omega)

private theorem opening_cap_pc (state : MachineState) :
    (openingCapState state).pc =
      if state.getReg .x28 - 1 = 0 then 4288 else 4208 := by
  rw [← (opening_cap_registers state).2.2]
  simp only [openingCapState, MachineState.getReg_setPC]
  simp only [MachineState.setPC]

/-- Iterated cap emission: pointers advance linearly and other registers persist. -/
theorem opening_cap_iterate_registers (iterations : Nat) (state : MachineState) :
    (openingCapState^[iterations] state).getReg .x23 =
      state.getReg .x23 + BitVec.ofNat 64 (96 * iterations) ∧
    (openingCapState^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (64 * iterations) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_cap_registers _).1,
      (opening_cap_registers _).2.1, ih.1, ih.2]
    constructor <;> simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

theorem opening_cap_preserves_register (iterations : Nat) (state : MachineState)
    (reg : Reg) (scratch : reg ≠ .x6) (source : reg ≠ .x23) (output : reg ≠ .x25)
    (counter : reg ≠ .x28) :
    (openingCapState^[iterations] state).getReg reg = state.getReg reg := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
    rw [Function.iterate_succ_apply',
      opening_cap_register _ reg scratch source output counter, ih]

/-- The complete cap loop has a precise linear cost and makes no queries. -/
theorem opening_cap_loop (remaining : Nat) (bounded : remaining ≤ 64)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4208)
    (sourceBound : (state.getReg .x23).toNat + 96 * remaining ≤ MEMORY_BYTES)
    (sourceAligned : (state.getReg .x23).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 64 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (20 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingCapState^[remaining] state) allowCoins
          return result.charge (20 * remaining) 0) := by
  induction remaining generalizing state with
  | zero => simp [Execution.charge]
  | succ remaining ih =>
    have small : remaining < 2 ^ 64 := by omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingCapState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_cap_registers state).2.2, counter, subtract]
    have nextPC : 0 < remaining → (openingCapState state).pc = 4208 := by
      intro positive
      rw [opening_cap_pc, counter, subtract, if_neg]
      intro zero
      have := congrArg BitVec.toNat zero
      change remaining % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt small] at this
      omega
    have sourceNat : ((openingCapState state).getReg .x23).toNat =
        (state.getReg .x23).toNat + 96 := by
      rw [(opening_cap_registers state).1, BitVec.toNat_add]
      change ((state.getReg .x23).toNat + 96) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at sourceBound
      omega
    have outputNat : ((openingCapState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 64 := by
      rw [(opening_cap_registers state).2.1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat + 64) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at outputBound
      omega
    have reads := opening_pair_access_valid (state.getReg .x23) (by omega) sourceAligned
    have writes := opening_pair_access_valid (state.getReg .x25) (by omega) outputAligned
    rw [show 20 * (remaining + 1) + fuel = 20 + (20 * remaining + fuel) by omega,
      opening_cap_iteration state (pc (by omega)) reads writes,
      ih (by omega) (openingCapState state) nextCounter nextPC
        (by rw [sourceNat]; omega) (by rw [sourceNat]; omega)
        (by rw [outputNat]; omega) (by rw [outputNat]; omega)]
    simp [Function.iterate_succ_apply, Execution.charge, Nat.mul_add, Nat.add_comm,
      Nat.add_left_comm]

/-- A positive cap counter reaches the branch to the empty-opening test. -/
theorem opening_cap_finished (remaining : Nat) (positive : 0 < remaining)
    (bounded : remaining ≤ 64) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (openingCapState^[remaining] state).pc = 4288 := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingCapState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_cap_registers state).2.2, counter, subtract]
    cases remaining with
    | zero =>
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
      rw [opening_cap_pc, counter, subtract]
      rfl
    | succ remaining =>
      rw [Function.iterate_succ_apply]
      exact ih (by omega) (by omega) (openingCapState state) nextCounter

private theorem opening_cap_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 64 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingCapState state).getMem address = state.getMem address := by
  apply opening_cap_memory_outside
  intro word equal
  have small : (state.getReg .x25).toNat + 8 * word.val < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at bounded
    omega
  have same := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 8 * word.val < 2 ^ 64), Nat.mod_eq_of_lt small] at same
  omega

/-- The cap loop never overwrites memory before its output pointer. -/
theorem opening_cap_loop_memory_below (iterations : Nat) (state : MachineState)
    (address : Word)
    (bounded : (state.getReg .x25).toNat + 64 * iterations ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingCapState^[iterations] state).getMem address = state.getMem address := by
  induction iterations generalizing state with
  | zero => rfl
  | succ iterations ih =>
    have outputNat : ((openingCapState state).getReg .x25).toNat =
        (state.getReg .x25).toNat + 64 := by
      rw [(opening_cap_registers state).2.1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat + 64) % 2 ^ 64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at bounded
      omega
    rw [Function.iterate_succ_apply, ih]
    · exact opening_cap_memory_below state address (by omega) below
    · rw [outputNat]; omega
    · rw [outputNat]; omega

private theorem opening_word_add (base offset : Nat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 offset = BitVec.ofNat 64 (base + offset) :=
  (BitVec.ofNat_add base offset).symm

/-- Every word of every emitted cap pair is the corresponding original heap word. -/
theorem opening_cap_records (count : Nat) (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x23 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (separated : source + 96 * count ≤ destination)
    (bounded : destination + 64 * count ≤ MEMORY_BYTES) :
    ∀ pair < count, ∀ word < 8,
      (openingCapState^[count] state).getMem
          (BitVec.ofNat 64 (destination + 64 * pair + 8 * word)) =
        state.getMem (BitVec.ofNat 64 (source + 96 * pair + 8 * word)) := by
  induction count generalizing state source destination with
  | zero => intro pair inside; omega
  | succ count ih =>
    have bound64 : destination + 64 * (count + 1) < 2 ^ 64 := by
      simp only [MEMORY_BYTES] at bounded
      omega
    let next := openingCapState state
    have nextSource : next.getReg .x23 = BitVec.ofNat 64 (source + 96) := by
      rw [(opening_cap_registers state).1, sourcePointer]
      exact opening_word_add source 96
    have nextDestination : next.getReg .x25 = BitVec.ofNat 64 (destination + 64) := by
      rw [(opening_cap_registers state).2.1, destinationPointer]
      exact opening_word_add destination 64
    have nextDestinationNat : (next.getReg .x25).toNat = destination + 64 := by
      rw [nextDestination, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    intro pair inside word wordBound
    rw [Function.iterate_succ_apply]
    cases pair with
    | zero =>
      have retained : (openingCapState^[count] next).getMem
          (BitVec.ofNat 64 (destination + 64 * 0 + 8 * word)) =
            next.getMem (BitVec.ofNat 64 (destination + 64 * 0 + 8 * word)) := by
        apply opening_cap_loop_memory_below
        · rw [nextDestinationNat]; omega
        · rw [nextDestinationNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
      have copied := opening_cap_memory state (by
        intro i j equal
        have iBound := i.isLt
        have jBound := j.isLt
        rw [sourcePointer, destinationPointer, opening_word_add, opening_word_add] at equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat] at natural
        rw [Nat.mod_eq_of_lt (by omega : source + 8 * i.val < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : destination + 8 * j.val < 2 ^ 64)] at natural
        omega) ⟨word, wordBound⟩
      rw [sourcePointer, destinationPointer, opening_word_add, opening_word_add] at copied
      simp only [Nat.mul_zero, Nat.add_zero] at retained ⊢
      exact retained.trans (by simpa only [Fin.val_mk] using copied)
    | succ pair =>
      have record := ih next (source + 96) (destination + 64) nextSource nextDestination
        (by omega) (by omega) pair (by omega) word wordBound
      have sourceKept : next.getMem (BitVec.ofNat 64 (source + 96 + 96 * pair + 8 * word)) =
          state.getMem (BitVec.ofNat 64 (source + 96 + 96 * pair + 8 * word)) := by
        apply opening_cap_memory_below
        · rw [destinationPointer, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : destination < 2 ^ 64)]
          omega
        · rw [destinationPointer, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : source + 96 + 96 * pair + 8 * word < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : destination < 2 ^ 64)]
          omega
      rw [show destination + 64 * (pair + 1) + 8 * word =
          destination + 64 + 64 * pair + 8 * word by omega,
        show source + 96 * (pair + 1) + 8 * word = source + 96 + 96 * pair + 8 * word by omega]
      exact record.trans sourceKept

/-! ### Complete setup -/

/-- State at the first position, or at the return block for an empty opening, after
setup and the complete 64-iteration cap emission. -/
def openingInitializedState (state : MachineState) : MachineState :=
  (openingCapState^[64] (openingCapStartState state)).setPC
    (if state.getReg .x16 = 0 then 4440 else 4292)

/-- Setup copies the ABI pointers and count, computes the heap size and salt base, and
leaves the output pointer just after the 4096-byte cap. -/
theorem opening_setup_registers (state : MachineState) :
    (openingInitializedState state).getReg .x9 = state.getReg .x12 ∧
    (openingInitializedState state).getReg .x24 = state.getReg .x13 ∧
    (openingInitializedState state).getReg .x25 = state.getReg .x15 + 4096 ∧
    (openingInitializedState state).getReg .x27 = state.getReg .x16 ∧
    (openingInitializedState state).getReg .x19 = 16777216 ∧
    (openingInitializedState state).getReg .x18 = state.getReg .x12 + 1610612736 ∧
    (openingInitializedState state).getReg .x16 = state.getReg .x16 := by
  have start := opening_cap_start_registers state
  have keep (reg : Reg) (scratch : reg ≠ .x6) (source : reg ≠ .x23) (output : reg ≠ .x25)
      (counter : reg ≠ .x28) :
      (openingInitializedState state).getReg reg = (openingCapStartState state).getReg reg := by
    simp only [openingInitializedState, MachineState.getReg_setPC]
    exact opening_cap_preserves_register 64 _ reg scratch source output counter
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep .x9 (by decide) (by decide) (by decide) (by decide), start.1]
  · rw [keep .x24 (by decide) (by decide) (by decide) (by decide), start.2.1]
  · simp only [openingInitializedState, MachineState.getReg_setPC]
    rw [(opening_cap_iterate_registers 64 _).2, start.2.2.1]
    rfl
  · rw [keep .x27 (by decide) (by decide) (by decide) (by decide), start.2.2.2.1]
  · rw [keep .x19 (by decide) (by decide) (by decide) (by decide), start.2.2.2.2.1]
  · rw [keep .x18 (by decide) (by decide) (by decide) (by decide), start.2.2.2.2.2.1]
  · rw [keep .x16 (by decide) (by decide) (by decide) (by decide), start.2.2.2.2.2.2.1]

/-- Setup and cap emission preserve all memory before the proof buffer. -/
theorem opening_setup_memory_below (state : MachineState) (address : Word)
    (outputBound : (state.getReg .x15).toNat + 4096 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x15).toNat) :
    (openingInitializedState state).getMem address = state.getMem address := by
  have start := opening_cap_start_registers state
  simp only [openingInitializedState, MachineState.getMem_setPC]
  rw [opening_cap_loop_memory_below 64 _ address (by rw [start.2.2.1]; omega)
    (by rw [start.2.2.1]; exact below)]
  simp only [MachineState.getMem, start.2.2.2.2.2.2.2.2.2]

/-- After setup, the first 4096 proof bytes hold the 64 cap pairs, read in heap order
from heap offset `6144 + 96k`. -/
theorem opening_setup_cap (state : MachineState) (heap proof : Nat)
    (heapPointer : state.getReg .x12 = BitVec.ofNat 64 heap)
    (proofPointer : state.getReg .x15 = BitVec.ofNat 64 proof)
    (separated : heap + 6144 + 96 * 64 ≤ proof)
    (bounded : proof + 4096 ≤ MEMORY_BYTES) :
    ∀ pair < 64, ∀ word < 8,
      (openingInitializedState state).getMem (BitVec.ofNat 64 (proof + 64 * pair + 8 * word)) =
        state.getMem (BitVec.ofNat 64 (heap + 6144 + 96 * pair + 8 * word)) := by
  have start := opening_cap_start_registers state
  intro pair inside word wordBound
  simp only [openingInitializedState, MachineState.getMem_setPC]
  rw [opening_cap_records 64 _ (heap + 6144) proof
    (by rw [start.2.2.2.2.2.2.2.1, heapPointer]; exact opening_word_add heap 6144)
    (by rw [start.2.2.1, proofPointer]) separated (by omega) pair inside word wordBound]
  simp only [MachineState.getMem, start.2.2.2.2.2.2.2.2.2]

/-- Exact 1309-cycle setup (28 setup instructions, 64 cap iterations of 20 cycles, and
the empty-opening test) from the actual image entry point. -/
theorem opening_setup (state : MachineState) (pc : state.pc = 4096)
    (heapBound : (state.getReg .x12).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x12).toNat % 8 = 0)
    (outputBound : (state.getReg .x15).toNat + 4096 ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x15).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (1309 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingInitializedState state) allowCoins
          return result.charge 1309 0) := by
  have start := opening_cap_start_registers state
  have sourceNat : ((openingCapStartState state).getReg .x23).toNat =
      (state.getReg .x12).toNat + 6144 := by
    rw [start.2.2.2.2.2.2.2.1, BitVec.toNat_add]
    change ((state.getReg .x12).toNat + 6144) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at heapBound
    omega
  have outputNat : ((openingCapStartState state).getReg .x25).toNat =
      (state.getReg .x15).toNat := by
    rw [start.2.2.1]
  have readyPC : (openingCapState^[64] (openingCapStartState state)).pc = 4288 :=
    opening_cap_finished 64 (by decide) (by decide) _ start.2.2.2.2.2.2.2.2.1
  have readyCount : (openingCapState^[64] (openingCapStartState state)).getReg .x27 =
      state.getReg .x16 := by
    rw [opening_cap_preserves_register 64 _ .x27 (by decide) (by decide) (by decide)
      (by decide)]
    exact start.2.2.2.1
  have fetched : fetch (submission.image .opening)
      (openingCapState^[64] (openingCapStartState state)) =
      some (.base (.BEQ .x27 .x0 152)) := by
    apply opening_fetch _ 48 _ (by decide) readyPC
    rfl
  have stepped : ordinaryStep (openingCapState^[64] (openingCapStartState state))
      (.base (.BEQ .x27 .x0 152)) = some (openingInitializedState state) := by
    dsimp only [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr]
    rw [readyCount, show (openingCapState^[64] (openingCapStartState state)).getReg .x0 = 0
      from rfl, readyPC]
    simp [openingInitializedState, signExtend13]
    split <;> simp_all
  rw [show 1309 + fuel = 28 + (20 * 64 + (fuel + 1)) by omega, opening_setup_prefix state pc,
    opening_cap_loop 64 (by decide) _ start.2.2.2.2.2.2.2.2.1
      (fun _ => opening_cap_start_pc state pc)
      (by rw [sourceNat]; omega) (by rw [sourceNat]; omega)
      (by rw [outputNat]; omega) (by rw [outputNat]; exact outputAligned),
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]


private def openingPathInstructions : List Instr :=
  [.XORI .x7 .x20 1, .SRLI .x6 .x20 1, .ADD .x7 .x7 .x6, .SLLI .x7 .x7 5, .ADD .x23 .x9 .x7]

private def openingPathPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPathInstructions.take count).foldl execInstrBr state

/-- Compute the sibling's gap-heap address: `t = s xor 1`, then `32*(t + s/2)`. -/
def openingPathPreparedState (state : MachineState) : MachineState :=
  openingPathPrefix state 5

private theorem opening_path_prepare (state : MachineState) (pc : state.pc = 4360)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathPreparedState state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingPathPrefix state)
  intro i hi
  refine ⟨.base ((openingPathInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (66 + i) _ (by omega)
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
    (state.getReg .x20 >>> 1)).setPC 4420

private theorem opening_path_advance (state : MachineState) (pc : state.pc = 4412)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPathAdvancedState state) allowCoins
          return result.charge 2 0) := by
  have first : fetch (submission.image .opening) state =
      some (.base (.ADDI .x25 .x25 32)) := by
    apply opening_fetch state 79 _ (by decide) pc
    rfl
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4416
  have second : fetch (submission.image .opening) next =
      some (.base (.SRLI .x20 .x20 1)) := by
    apply opening_fetch next 80 _ (by decide) rfl
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

/-- Exact seventeen-cycle iteration of the submitted opening program. -/
theorem opening_path_iteration (state : MachineState) (pc : state.pc = 4360)
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
  have readyPC : ready.pc = 4380 := by
    simp [ready, openingPathPreparedState, openingPathPrefix, openingPathInstructions,
      execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4412 := by rw [opening_copy_pc, readyPC]; rfl
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
    opening_copy ready 71 rfl readyPC reads writes,
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


/-- The sibling's byte offset in the gap heap, as computed by the path loop. -/
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

/-- Sibling addresses remain inside the allocated gap heap: every node below 2^25
lies in the first 96*2^24 bytes (including unused slot zero and the zero gaps). -/
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
      if state.getReg .x28 - 1 = 0 then 4428 else 4360 := by
  simp [openingPathState, openingLatchState, openingPathAdvancedState,
    copy_pc_setPC, MachineState.getReg_setReg_ne,
    opening_copy_register, opening_path_prepare_register]

/-- The complete sibling loop has a precise linear cost. Its assumptions are
ordinary heap/output bounds and alignment; the memory contents are arbitrary. -/
theorem opening_path_loop (remaining : Nat) (bounded : remaining ≤ LOG_LENGTH)
    (state : MachineState) (counter : state.getReg .x28 = BitVec.ofNat 64 remaining)
    (pc : 0 < remaining → state.pc = 4360)
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
      simp only [LOG_LENGTH] at bounded
      omega
    have subtract : BitVec.ofNat 64 (remaining + 1) - 1 = BitVec.ofNat 64 remaining := by
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      simp
    have nextCounter : (openingPathState state).getReg .x28 = BitVec.ofNat 64 remaining := by
      rw [(opening_path_registers state).2.2.1, counter, subtract]
    have nextPC : 0 < remaining → (openingPathState state).pc = 4360 := by
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


/-- A positive path counter reaches zero and transfers control to `open-next`
after exactly that many iterations. -/
theorem opening_path_finished (remaining : Nat) (positive : 0 < remaining)
    (bounded : remaining ≤ LOG_LENGTH) (state : MachineState)
    (counter : state.getReg .x28 = BitVec.ofNat 64 remaining) :
    (openingPathState^[remaining] state).pc = 4428 ∧
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
  [.LD .x20 .x24 0, .SLLI .x6 .x20 3, .SLLI .x7 .x20 4, .ADD .x6 .x6 .x7, .ADD .x23 .x18 .x6]

private def openingPositionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingPositionInstructions.take count).foldl execInstrBr state

/-- Read the next serialized position and compute its salt address `x18 + 8i + 16i`. -/
def openingPositionPreparedState (state : MachineState) : MachineState :=
  openingPositionPrefix state 5

private theorem opening_position_prepare (state : MachineState) (pc : state.pc = 4292)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPreparedState state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := openingPositionPrefix state)
  intro i hi
  refine ⟨.base ((openingPositionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (49 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingPositionPrefix, openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i
    · simpa [openingPositionPrefix, openingPositionInstructions, ordinaryStep,
        memoryArgumentsValid, memAccess, signExtend12] using indexValid
    all_goals rfl
  · interval_cases i <;> rfl

theorem opening_position_prepare_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (index : reg ≠ .x20) (source : reg ≠ .x23) (sibling : reg ≠ .x7) :
    (openingPositionPreparedState state).getReg reg = state.getReg reg := by
  dsimp only [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
    List.take, List.foldl, execInstrBr]
  simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm sibling),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm index),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source)]

theorem opening_position_prepared (state : MachineState) :
    (openingPositionPreparedState state).getReg .x20 = state.getMem (state.getReg .x24) ∧
    (openingPositionPreparedState state).getReg .x23 =
      state.getReg .x18 + ((state.getMem (state.getReg .x24) <<< 3) +
        (state.getMem (state.getReg .x24) <<< 4)) := by
  simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq, signExtend12]

/-- The 24-byte salt copy: three aligned loads and stores, x6 scratch. -/
private def openingSaltCopyInstructions : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .LD .x6 .x23 8, .SD .x25 .x6 8,
   .LD .x6 .x23 16, .SD .x25 .x6 16]

private def openingSaltCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSaltCopyInstructions.take count).foldl execInstrBr state

/-- State after copying one 24-byte salt. -/
def openingSaltCopyState (state : MachineState) : MachineState :=
  openingSaltCopyPrefix state 6

private theorem opening_salt_copy_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingSaltCopyPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [openingSaltCopyPrefix, openingSaltCopyInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, copy_getReg_setMem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem opening_salt_copy_register (state : MachineState) (reg : Reg) (scratch : reg ≠ .x6) :
    (openingSaltCopyState state).getReg reg = state.getReg reg :=
  opening_salt_copy_prefix_register state 6 (by decide) reg scratch

set_option maxHeartbeats 1000000 in
/-- The salt copy in the actual image takes six cycles and makes no queries. -/
theorem opening_salt_copy (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * 54))
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltCopyState state) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := openingSaltCopyPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (54 + i) _ (by omega)
    · interval_cases i <;>
        simp [openingSaltCopyPrefix, openingSaltCopyInstructions, execInstrBr, pc,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have sourceReg := opening_salt_copy_prefix_register state i (by omega) .x23 (by decide)
    have destinationReg := opening_salt_copy_prefix_register state i (by omega) .x25 (by decide)
    have valid : memoryArgumentsValid (openingSaltCopyPrefix state i)
        ((openingSaltCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid, memAccess,
          sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact d0 | exact d1 | exact d2
    interval_cases i <;>
      simp only [openingSaltCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- Outside the three destination words, copying a salt leaves memory unchanged. -/
theorem opening_salt_copy_memory_outside (state : MachineState) (address : Word)
    (outside : ∀ word : Fin 3,
      address ≠ state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) :
    (openingSaltCopyState state).getMem address = state.getMem address := by
  have h0 := outside ⟨0, by decide⟩
  have h1 := outside ⟨1, by decide⟩
  have h2 := outside ⟨2, by decide⟩
  have a0 : address ≠ state.getReg .x25 := by simpa using h0
  have a1 : address ≠ state.getReg .x25 + 8#64 := h1
  have a2 : address ≠ state.getReg .x25 + 16#64 := h2
  simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
    execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    copy_getReg_setMem, copy_getMem_setMem, signExtend12, a0, a1, a2]

/-- With disjoint source and destination words, the salt copy writes the three original
source words to their corresponding destination addresses. -/
theorem opening_salt_copy_memory (state : MachineState)
    (separated : ∀ source destination : Fin 3,
      state.getReg .x23 + BitVec.ofNat 64 (8 * source.val) ≠
        state.getReg .x25 + BitVec.ofNat 64 (8 * destination.val)) (word : Fin 3) :
    (openingSaltCopyState state).getMem (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) := by
  have h10 : state.getReg .x23 + 8#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨1, by decide⟩ ⟨0, by decide⟩
  have h20 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 := by
    simpa using separated ⟨2, by decide⟩ ⟨0, by decide⟩
  have h21 : state.getReg .x23 + 16#64 ≠ state.getReg .x25 + 8#64 :=
    separated ⟨2, by decide⟩ ⟨1, by decide⟩
  fin_cases word <;>
    simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
      execInstrBr, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      copy_getReg_setMem, signExtend12, h10, h20, h21]

theorem opening_salt_copy_pc (state : MachineState) :
    (openingSaltCopyState state).pc = state.pc + 24 := by
  simp [openingSaltCopyState, openingSaltCopyPrefix, openingSaltCopyInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

private def openingSaltInstructions : List Instr :=
  [.ADDI .x25 .x25 24, .ADD .x20 .x20 .x19, .ADDI .x28 .x0 0,
   .SLLI .x28 .x28 11, .ADDI .x28 .x28 17, .BEQ .x28 .x0 72]

private def openingSaltPrefix (state : MachineState) (count : Nat) : MachineState :=
  (openingSaltInstructions.take count).foldl execInstrBr state

/-- After the salt copy, advance the proof pointer, enter the leaf's heap slot,
and set the sibling-loop counter to 17. -/
def openingSaltAdvancedState (state : MachineState) : MachineState :=
  openingSaltPrefix state 6

private theorem opening_salt_advance (state : MachineState) (pc : state.pc = 4336)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingSaltAdvancedState state) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := openingSaltPrefix state)
  intro i hi
  refine ⟨.base ((openingSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply opening_fetch _ (60 + i) _ (by omega)
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
    (openingSaltAdvancedState state).getReg .x25 = state.getReg .x25 + 24 ∧
    (openingSaltAdvancedState state).getReg .x20 = state.getReg .x20 + state.getReg .x19 ∧
    (openingSaltAdvancedState state).getReg .x28 = 17 ∧
    (openingSaltAdvancedState state).pc = state.pc + 24 := by
  simp [openingSaltAdvancedState, openingSaltPrefix, openingSaltInstructions,
    execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
    signExtend12, BitVec.add_assoc]

/-- State at the sibling-loop entry after copying this position's salt. -/
def openingPositionPathState (state : MachineState) : MachineState :=
  openingSaltAdvancedState (openingSaltCopyState (openingPositionPreparedState state))

/-- The actual position setup and salt copy take seventeen cycles. -/
theorem opening_position_setup (state : MachineState) (pc : state.pc = 4292)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (sourceValid : ∀ word : Fin 3,
      accessValid (state.getReg .x18 + ((state.getMem (state.getReg .x24) <<< 3) +
        (state.getMem (state.getReg .x24) <<< 4)) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (17 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionPathState state) allowCoins
          return result.charge 17 0) := by
  let ready := openingPositionPreparedState state
  let copied := openingSaltCopyState ready
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * 54) := by
    simp [ready, openingPositionPreparedState, openingPositionPrefix,
      openingPositionInstructions, execInstrBr, pc, MachineState.setPC]
  have copiedPC : copied.pc = 4336 := by rw [opening_salt_copy_pc, readyPC]; rfl
  have reads : ∀ word : Fin 3,
      accessValid (ready.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [(opening_position_prepared state).2]
    exact sourceValid word
  have writes : ∀ word : Fin 3,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide) (by decide)]
    exact destinationValid word
  rw [show 17 + fuel = 5 + (6 + (6 + fuel)) by omega,
    opening_position_prepare state pc indexValid,
    opening_salt_copy ready readyPC reads writes,
    opening_salt_advance copied copiedPC]
  simp [openingPositionPathState, ready, copied, Execution.charge, ← Nat.add_assoc]


theorem opening_position_path_register (state : MachineState) (reg : Reg)
    (scratch : reg ≠ .x6) (index : reg ≠ .x20) (source : reg ≠ .x23)
    (output : reg ≠ .x25) (counter : reg ≠ .x28) (sibling : reg ≠ .x7) :
    (openingPositionPathState state).getReg reg = state.getReg reg := by
  rw [openingPositionPathState, opening_salt_register _ reg output index counter,
    opening_salt_copy_register _ reg scratch,
    opening_position_prepare_register _ reg scratch index source sibling]

theorem opening_position_path_registers (state : MachineState) :
    (openingPositionPathState state).getReg .x25 = state.getReg .x25 + 24 ∧
    (openingPositionPathState state).getReg .x20 =
      state.getMem (state.getReg .x24) + state.getReg .x19 ∧
    (openingPositionPathState state).getReg .x28 = 17 := by
  refine ⟨?_, ?_, (opening_salt_advanced _).2.2.1⟩
  · rw [openingPositionPathState, (opening_salt_advanced _).1,
      opening_salt_copy_register _ .x25 (by decide),
      opening_position_prepare_register _ .x25 (by decide) (by decide) (by decide) (by decide)]
  · rw [openingPositionPathState, (opening_salt_advanced _).2.1,
      opening_salt_copy_register _ .x20 (by decide), opening_salt_copy_register _ .x19 (by decide),
      (opening_position_prepared state).1,
      opening_position_prepare_register _ .x19 (by decide) (by decide) (by decide) (by decide)]

/-- The computed salt address is `salts + 24 * index`, without wraparound. -/
theorem opening_salt_address (salts index : Word)
    (saltBound : salts.toNat + 2 ^ 29 ≤ MEMORY_BYTES) (indexBound : index.toNat < 2 ^ 24) :
    (salts + ((index <<< 3) + (index <<< 4))).toNat = salts.toNat + 24 * index.toNat := by
  have offset3 : (index <<< 3).toNat = index.toNat * 8 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (index.toNat * 8) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt]
    omega
  have offset4 : (index <<< 4).toNat = index.toNat * 16 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (index.toNat * 16) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt]
    omega
  have sum : ((index <<< 3) + (index <<< 4)).toNat = 24 * index.toNat := by
    rw [BitVec.toNat_add, offset3, offset4, Nat.mod_eq_of_lt (by omega)]
    omega
  have total : salts.toNat + 24 * index.toNat < 2 ^ 64 := by
    simp only [MEMORY_BYTES] at saltBound
    omega
  rw [BitVec.toNat_add, sum, Nat.mod_eq_of_lt total]

/-- Salt lookup is safe for every valid vector index, independently of salt contents. -/
theorem opening_salt_access (salts index : Word)
    (saltBound : salts.toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : salts.toNat % 8 = 0) (indexBound : index.toNat < 2 ^ 24)
    (word : Fin 3) :
    accessValid (salts + ((index <<< 3) + (index <<< 4)) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
  have address := opening_salt_address salts index saltBound indexBound
  have valid := opening_digest_access_valid (salts + ((index <<< 3) + (index <<< 4)))
    (by rw [address]; omega) (by rw [address]; omega) ⟨word.val, by omega⟩
  simpa using valid

/-- State after one complete salt-plus-path opening and the outer loop latch. -/
def openingPositionState (state : MachineState) : MachineState :=
  openingNextState (openingPathState^[17] (openingPositionPathState state))

/-- One complete position costs 309 cycles and makes no queries, including its
salt, all 17 siblings, and the transition to the next position or return block. -/
theorem opening_position (state : MachineState) (pc : state.pc = 4292)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (indexBound : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 568 ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (309 + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState state) allowCoins
          return result.charge 309 0) := by
  let path := openingPositionPathState state
  have pathPC : path.pc = 4360 := by
    change (openingPositionPathState state).pc = 4360
    rw [openingPositionPathState, (opening_salt_advanced _).2.2.2, opening_salt_copy_pc]
    simp [openingPositionPreparedState, openingPositionPrefix, openingPositionInstructions,
      execInstrBr, pc, MachineState.setPC]
  have pathCounter : path.getReg .x28 = BitVec.ofNat 64 17 :=
    (opening_position_path_registers state).2.2
  have pathHeap : path.getReg .x9 = state.getReg .x9 :=
    opening_position_path_register state .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have pathNode : (path.getReg .x20).toNat < 2 ^ 25 := by
    rw [(opening_position_path_registers state).2.1, leaves, BitVec.toNat_add]
    change ((state.getMem (state.getReg .x24)).toNat + 16777216) % 2 ^ 64 < 2 ^ 25
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 24 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 24) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    simp only [MEMORY_BYTES] at outputBound
    omega
  have pathOutput : (path.getReg .x25).toNat + 32 * 17 ≤ MEMORY_BYTES := by
    rw [outputNat]; omega
  have pathAligned : (path.getReg .x25).toNat % 8 = 0 := by rw [outputNat]; omega
  have finishedPC : (openingPathState^[17] path).pc = 4428 :=
    (opening_path_finished 17 (by decide) (by decide) path pathCounter).1
  have reads := opening_salt_access (state.getReg .x18) (state.getMem (state.getReg .x24))
    saltBound saltAligned indexBound
  have writes : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => opening_digest_access_valid (state.getReg .x25) (by omega) outputAligned
      ⟨word.val, by omega⟩
  rw [show 309 + fuel = 17 + (17 * 17 + (3 + fuel)) by omega,
    opening_position_setup state pc indexValid reads writes,
    opening_path_loop 17 (by decide) path pathCounter (fun _ => pathPC)
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

/-- The sibling loop emits one 32-byte digest per level. -/
theorem opening_path_output (iterations : Nat) (state : MachineState) :
    (openingPathState^[iterations] state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (32 * iterations) := by
  induction iterations with
  | zero => simp
  | succ iterations ih =>
    rw [Function.iterate_succ_apply', (opening_path_registers _).1, ih]
    simp [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- One position advances the input by eight bytes and the proof by 568 bytes,
while decrementing the number of positions still to open. -/
theorem opening_position_progress (state : MachineState) :
    (openingPositionState state).getReg .x24 = state.getReg .x24 + 8 ∧
    (openingPositionState state).getReg .x25 = state.getReg .x25 + 568 ∧
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
      if state.getReg .x27 - 1 = 0 then 4440 else 4292 := by
  simp [-Function.iterate_succ, openingPositionState, openingNextState, copy_pc_setPC,
    opening_path_preserves_register, opening_position_path_register]

private theorem opening_salt_copy_memory_below (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat + 24 ≤ MEMORY_BYTES)
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
    (bounded : (state.getReg .x25).toNat + 568 ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPositionState state).getMem address = state.getMem address := by
  let path := openingPositionPathState state
  have outputNat : (path.getReg .x25).toNat = (state.getReg .x25).toNat + 24 := by
    rw [(opening_position_path_registers state).1, BitVec.toNat_add]
    change ((state.getReg .x25).toNat + 24) % 2 ^ 64 = _
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
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide) (by decide)]
        using (show (state.getReg .x25).toNat + 24 ≤ MEMORY_BYTES by omega)
    · simpa only [opening_position_prepare_register state .x25 (by decide) (by decide) (by decide) (by decide)] using below
  simp only [openingPositionState, openingNextState, MachineState.getMem_setPC, MachineState.getMem_setReg]
  rw [opening_path_loop_memory_below 17 path address, saltMemory]
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
    (pc : 0 < remaining → state.pc = 4292)
    (indices : ∀ offset < remaining,
      (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24)
    (indexSpace : (state.getReg .x24).toNat + 8 * remaining ≤ (state.getReg .x25).toNat)
    (indexAligned : (state.getReg .x24).toNat % 8 = 0)
    (leaves : state.getReg .x19 = 16777216)
    (saltBound : (state.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES)
    (saltAligned : (state.getReg .x18).toNat % 8 = 0)
    (heapBound : (state.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES)
    (heapAligned : (state.getReg .x9).toNat % 8 = 0)
    (outputBound : (state.getReg .x25).toNat + 568 * remaining ≤ MEMORY_BYTES)
    (outputAligned : (state.getReg .x25).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .opening) (309 * remaining + fuel) state allowCoins =
      (do let result ← execute (submission.image .opening) fuel
            (openingPositionState^[remaining] state) allowCoins
          return result.charge (309 * remaining) 0) := by
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
    have nextPC : 0 < remaining → (openingPositionState state).pc = 4292 := by
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
        (state.getReg .x25).toNat + 568 := by
      rw [(opening_position_progress state).2.1]
      exact opening_address_add (state.getReg .x25) 568 (by omega)
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
    rw [show 309 * (remaining + 1) + fuel = 309 + (309 * remaining + fuel) by omega,
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
    (openingPositionState^[remaining] state).pc = 4440 ∧
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

end CommitGolfCandidate
