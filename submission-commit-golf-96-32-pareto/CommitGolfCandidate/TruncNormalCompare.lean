import CommitGolfCandidate.TruncNormalEntry
namespace CommitGolfCandidate.Trunc.Normal
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
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
    · apply sharedFetch _ (start + 3 * word + i) _ (by unfold untouched;rcases location with rfl | rfl <;> omega)
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
    apply sharedFetch _ (start + 3 * word + 2) _ (by unfold untouched;rcases location with rfl | rfl <;> omega)
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

end CommitGolfCandidate.Trunc.Normal
