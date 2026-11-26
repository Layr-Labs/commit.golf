import CommitGolfCandidate.LateNormalPad
import CommitGolfCandidate.CKBTcomp
import CommitGolfCandidate.CKNHalf

namespace CommitGolfCandidate.Late.Check.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

theorem check_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 814) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((checkerImage).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (checkerImage) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (checkerImage).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

def checkExitState (state : MachineState) (success : Bool) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 (if success then 0 else 1)).setPC
    (if success then 4428 else 4440)

theorem check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 4420 else 4432) (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure, checkExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 4424 else 4436)
  have fetch₁ : fetch (checkerImage) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply check_fetch state 84 _ (by decide) pc; rfl
    · apply check_fetch state 81 _ (by decide) pc; rfl
  have fetch₂ : fetch (checkerImage) next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply check_fetch next 85 _ (by decide) rfl; rfl
    · apply check_fetch next 82 _ (by decide) rfl; rfl
  have fetch₃ : fetch (checkerImage) (checkExitState state success) =
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

def checkRootInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x21 (BitVec.ofNat 12 (8 * word)), .LD .x7 .x23 (BitVec.ofNat 12 (8 * word))]

def checkRootPrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((checkRootInstructions word).take count).foldl execInstrBr state

def checkRootBranchOffset (start word : Nat) : BitVec 13 :=
  BitVec.ofNat 13 ((if start = 66 then 64 else 7968) - 12 * word)

def checkRootWordState (state : MachineState) (start word : Nat) : MachineState :=
  execInstrBr (checkRootPrefix state word 2) (.BNE .x6 .x7 (checkRootBranchOffset start word))

theorem check_root_word (state : MachineState) (start word : Nat)
    (location : start = 66 ∨ start = 138) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (3 + fuel) state allowCoins =
      (do let result ← execute (checkerImage) fuel
            (checkRootWordState state start word) allowCoins
          return result.charge 3 0) := by
  have loads (remaining : Nat) : execute (checkerImage) (2 + remaining) state allowCoins =
      (do let result ← execute (checkerImage) remaining
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
  have fetched : fetch (checkerImage) (checkRootPrefix state word 2) =
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
    execute (checkerImage) (6 + fuel) state allowCoins =
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

theorem check_root_words_read (state : MachineState) (start count word : Nat) (reg : Reg)
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
    execute (checkerImage) (3 * count + remaining) state allowCoins =
      (do let result ← execute (checkerImage) remaining
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
    execute (checkerImage) (12 + fuel) state allowCoins =
      (do let result ← execute (checkerImage) fuel
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
    execute (checkerImage) (3 * word + 6 + fuel) state allowCoins =
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
    ∃ result, execute (checkerImage) (15 + fuel) state allowCoins = pure result ∧
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

def checkCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

def checkCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (checkCompressionInstructions.take count).foldl execInstrBr state

/-- The padded compression written at 256 (before the truncation tail). -/
def checkPaddedState (state : MachineState) (answer : BitVec 256) : MachineState :=
  let ready := checkCompressionPrefix state 5
  writeBits ((savePaddingRegisters (ready.setReg .x31 (ready.pc+4))).setReg .x11 64) 256 answer

/-- The 5-instruction setup followed by the truncating adapter `tcomp` (438): bit 0 of x9 selects
the 240-bit store (`sh x0,30(x12)` clears bytes 286, 287); x9 shifts right; x7 is the bit. -/
def checkCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  let base := ((checkPaddedState state answer).setReg .x7 (tcompBit state)).setReg .x9 (state.getReg .x9 >>> 1)
  if tcompBit state = 0 then base else base.setHalfword (BitVec.ofNat 64 286) 0

theorem check_compression_prefix_x9 (state : MachineState) :
    (checkCompressionPrefix state 5).getReg .x9 = state.getReg .x9 := by
  simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne]

theorem check_compression (state : MachineState) (start : Nat)
    (location : start = 54 ∨ start = 537 ∨ start = 621)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (checkerImage) (5 + tcompSteps state + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer state 256 64))))
          let result ← execute (checkerImage) fuel (checkCompressionState state answer) allowCoins
          return result.charge (12 + tcompSteps state) 1) := by
  have setup (remaining : Nat) :
      execute (checkerImage) (5 + remaining) state allowCoins =
        (do let result ← execute (checkerImage) remaining
              (checkCompressionPrefix state 5) allowCoins
            return result.charge 5 0) := by
    apply execute_unit_steps (states := checkCompressionPrefix state)
    intro i hi
    refine ⟨.base ((checkCompressionInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply check_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl <;> omega)
      · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
          simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let ready := checkCompressionPrefix state 5
  have readyPC : ready.pc = BitVec.ofNat 64 (4096 + 4 * (start+5)) := by
    dsimp only [ready]
    rcases location with rfl | rfl | rfl <;>
        simp [checkCompressionPrefix, checkCompressionInstructions, execInstrBr, pc, MachineState.setPC]
  have registers : ready.getReg .x5 = 0 ∧ ready.getReg .x10 = 256 ∧
      ready.getReg .x11 = 64 ∧ ready.getReg .x12 = 256 ∧ ready.getReg .x13 = 0 := by
    simp [ready, checkCompressionPrefix, checkCompressionInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, scratch]
    rfl
  have mask : ready.getReg .x9 = state.getReg .x9 := check_compression_prefix_x9 state
  have steps : tcompSteps ready = tcompSteps state := by
    unfold tcompSteps tcompBit; rw [mask]
  have call := tcomp_call ready (start+5)
    (by rcases location with rfl | rfl | rfl <;> simp) readyPC
    registers.1 registers.2.2.2.2
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1]; rfl) (by rw [registers.2.2.2.1]; rfl)
    (by rw [registers.2.1, registers.2.2.2.1]; decide) fuel allowCoins
  rw [show 5 + tcompSteps state + fuel = 5 + (tcompSteps ready + fuel) by rw [steps]; omega, setup]
  erw [call]
  simp only [bind_assoc, pure_bind]
  rw [registers.2.1]
  change ((liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64)))))) >>= _) = _
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer state 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have bit : tcompBit ready = tcompBit state := by simp only [tcompBit, mask]
  have resultState : tcompState ready answer = checkCompressionState state answer := by
    unfold tcompState paddedCompressionState checkCompressionState checkPaddedState
    rw [registers.2.2.2.1, bit, mask]
    rfl
  rw [resultState, steps]
  simp [Execution.charge, ← Nat.add_assoc]
  congr 1
  funext a
  congr 1
  omega

theorem check_compression_pc (state : MachineState) (answer : BitVec 256) :
    (checkCompressionState state answer).pc = state.pc + 24 := by
  unfold checkCompressionState
  split <;>
  simp [checkPaddedState, writeBits, savePaddingRegisters, checkCompressionPrefix, checkCompressionInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc, MachineState.pc_setReg, MachineState.setHalfword]

theorem check_padded_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
    (not14 : reg ≠ .x14 := by decide) (not15 : reg ≠ .x15 := by decide)
    (not16 : reg ≠ .x16 := by decide) (not17 : reg ≠ .x17 := by decide)
    (not31 : reg ≠ .x31 := by decide) :
    (checkPaddedState state answer).getReg reg = state.getReg reg := by
  rw [checkPaddedState, writeBits_register]
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

theorem check_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not10 : reg ≠ .x10) (not11 : reg ≠ .x11)
    (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
    (not14 : reg ≠ .x14 := by decide) (not15 : reg ≠ .x15 := by decide)
    (not16 : reg ≠ .x16 := by decide) (not17 : reg ≠ .x17 := by decide)
    (not31 : reg ≠ .x31 := by decide) (not7 : reg ≠ .x7 := by decide) (not9 : reg ≠ .x9 := by decide) :
    (checkCompressionState state answer).getReg reg = state.getReg reg := by
  have base : (((checkPaddedState state answer).setReg .x7 (tcompBit state)).setReg .x9
      (state.getReg .x9 >>> 1)).getReg reg = state.getReg reg := by
    rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not9),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not7)]
    exact check_padded_register state answer reg not5 not10 not11 not12 not13 not14 not15 not16 not17 not31
  unfold checkCompressionState
  split
  · exact base
  · exact (CKNHalf.ckn_set_halfword_reg _ _ _ _).trans base

theorem check_compression_x9 (state : MachineState) (answer : BitVec 256) :
    (checkCompressionState state answer).getReg .x9 = state.getReg .x9 >>> 1 := by
  have base : (((checkPaddedState state answer).setReg .x7 (tcompBit state)).setReg .x9
      (state.getReg .x9 >>> 1)).getReg .x9 = state.getReg .x9 >>> 1 :=
    MachineState.getReg_setReg_eq (by decide)
  unfold checkCompressionState
  split
  · exact base
  · exact (CKNHalf.ckn_set_halfword_reg _ _ _ _).trans base

theorem check_padded_word (state : MachineState) (answer : BitVec 256)
    (word : Nat) (bounded : word < 4) :
    (checkPaddedState state answer).getMem (BitVec.ofNat 64 (256 + 8 * word)) =
      answer.extractLsb' (64 * word) 64 := by
  have byte (i : Nat) : BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)) =
      answer.extractLsb' (8 * i) 8 := by
    apply BitVec.toNat_inj.mp
    simp [Nat.shiftRight_eq_div_pow]
  unfold checkPaddedState writeBits
  simp_rw [byte]
  interval_cases word <;>
    simp [List.range_succ, MachineState.setPC, MachineState.setByte,
      MachineState.setMem, MachineState.getMem, alignToDword, byteOffset, replaceByte] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;>
    interval_cases bit <;>
    simp

theorem check_padded_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkPaddedState state answer) 256 32 = answer := by
  rw [read_digest_words _ _ (by decide)]
  have w0 := check_padded_word state answer 0 (by decide)
  have w1 := check_padded_word state answer 1 (by decide)
  have w2 := check_padded_word state answer 2 (by decide)
  have w3 := check_padded_word state answer 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

/-- The digest left at 256: full, or its low 240 bits when bit 0 of x9 was set. -/
def tcompDigest (bit : Word) (answer : BitVec 256) : BitVec 256 :=
  if bit = 0 then answer else widen (low240 answer)

theorem check_compression_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkCompressionState state answer) 256 32 = tcompDigest (tcompBit state) answer := by
  have base : readBuffer (((checkPaddedState state answer).setReg .x7 (tcompBit state)).setReg .x9
      (state.getReg .x9 >>> 1)) 256 32 = answer :=
    (CKNHalf.ckn_read_set_reg _ _ _ _ _).trans ((CKNHalf.ckn_read_set_reg _ _ _ _ _).trans (check_padded_digest state answer))
  unfold checkCompressionState tcompDigest
  split
  · exact base
  · rw [CKNHalf.ckn_zero_top_digest, base]

theorem check_padded_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkPaddedState state answer).getMem address = state.getMem address := by
  unfold checkPaddedState
  rw [writeBits_memory_outside]
  · rfl
  · intro i hi
    change i < 32 at hi
    interval_cases i <;> norm_num [alignToDword] <;> tauto

theorem check_compression_memory_outside (state : MachineState) (answer : BitVec 256)
    (address : Word) (outside : address ≠ 256 ∧ address ≠ 264 ∧ address ≠ 272 ∧ address ≠ 280) :
    (checkCompressionState state answer).getMem address = state.getMem address := by
  have base : (((checkPaddedState state answer).setReg .x7 (tcompBit state)).setReg .x9
      (state.getReg .x9 >>> 1)).getMem address = state.getMem address :=
    check_padded_memory_outside state answer address outside
  unfold checkCompressionState
  split
  · exact base
  · exact (CKNHalf.ckn_zero_top_mem _ _ outside.2.2.2).trans base

end CommitGolfCandidate.Late.Check.Normal
