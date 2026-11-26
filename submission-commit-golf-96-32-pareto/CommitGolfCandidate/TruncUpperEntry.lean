import CommitGolfCandidate.PairUpper
import CommitGolfCandidate.TruncCheckPad
import CommitGolfCandidate.TruncCapGuard
import CommitGolfCandidate.TruncMask
import CommitGolfCandidate.TruncModel
namespace CommitGolfCandidate.Trunc.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.PairCap
set_option maxRecDepth 13000
set_option maxHeartbeats 350000


theorem top_check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 5720 else 4432) (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure, top_checkExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 5724 else 4436)
  have fetch₁ : fetch (Trunc.submission.image .check) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply sharedFetch state 84 _ (by unfold untouched; decide) pc; rfl
    · apply sharedFetch state 406 _ (by unfold untouched; decide) pc; rfl
  have fetch₂ : fetch (Trunc.submission.image .check) next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply sharedFetch next 85 _ (by unfold untouched; decide) rfl; rfl
    · apply sharedFetch next 407 _ (by unfold untouched; decide) rfl; rfl
  have fetch₃ : fetch (Trunc.submission.image .check) (top_checkExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply sharedFetch _ 86 _ (by unfold untouched; decide) rfl; rfl
    · apply sharedFetch _ 408 _ (by unfold untouched; decide) rfl; rfl
  have step₁ : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, pc, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have step₂ : ordinaryStep next (.base (.ADDI .x10 .x0 (if success then 0 else 1))) =
      some (top_checkExitState state success) := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, top_checkExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, fetch₁, step₁, fetch₂, step₂, fetch₃, instructionCycles,
    bind_assoc, pure_bind]
  cases success <;> simp [top_checkExitState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

theorem top_check_root_word (state : MachineState) (start word : Nat)
    (location : start = 294 ∨ start = 394) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) fuel
            (top_checkRootWordState state start word) allowCoins
          return result.charge 3 0) := by
  have loads (remaining : Nat) : execute (Trunc.submission.image .check) (2 + remaining) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) remaining
            (top_checkRootPrefix state word 2) allowCoins
          return result.charge 2 0) := by
    apply execute_unit_steps (states := top_checkRootPrefix state word)
    intro i hi
    refine ⟨.base (((top_checkRootInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply sharedFetch _ (start + 3 * word + i) _ (by unfold untouched; rcases location with rfl | rfl <;> omega)
      · rcases location with rfl | rfl <;> interval_cases word <;> interval_cases i <;>
          simp [top_checkRootPrefix, top_checkRootInstructions, execInstrBr, pc, MachineState.setPC]
      · rcases location with rfl | rfl <;> interval_cases word <;> interval_cases i <;> rfl
    · have offset : signExtend12 (BitVec.ofNat 12 (8 * word)) = BitVec.ofNat 64 (8 * word) := by
        interval_cases word <;> rfl
      interval_cases i <;>
        simp only [top_checkRootPrefix, top_checkRootInstructions, List.take, List.foldl,
          List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
          ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, offset,
          MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23)] <;>
        first | rw [scratchValid]; rfl | rw [targetValid]; rfl
    · interval_cases i <;> rfl
  have fetched : fetch (Trunc.submission.image .check) (top_checkRootPrefix state word 2) =
      some (.base (.BNE .x6 .x7 (top_checkRootBranchOffset start word))) := by
    apply sharedFetch _ (start + 3 * word + 2) _ (by unfold untouched; rcases location with rfl | rfl <;> omega)
    · rcases location with rfl | rfl <;> interval_cases word <;>
        simp [top_checkRootPrefix, top_checkRootInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl <;> interval_cases word <;> rfl
  have stepped : ordinaryStep (top_checkRootPrefix state word 2)
      (.base (.BNE .x6 .x7 (top_checkRootBranchOffset start word))) =
        some (top_checkRootWordState state start word) := rfl
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, loads]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem top_check_root_word_reject (state : MachineState) (start word : Nat)
    (location : start = 294 ∨ start = 394) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (6 + fuel) state allowCoins =
      pure ⟨.failure, top_checkExitState (top_checkRootWordState state start word) false, 6, 0⟩ := by
  have rejectPC : (top_checkRootWordState state start word).pc = 4432 := by
    rw [top_check_root_word_pc state start word location bounded pc, if_neg different]
  rw [show 6 + fuel = 3 + (3 + fuel) by omega,
    top_check_root_word state start word location bounded pc scratchValid targetValid,
    top_check_exit _ false rejectPC]
  simp [Execution.charge]

theorem top_check_root_prefix (state : MachineState) (start : Nat)
    (location : start = 294 ∨ start = 394)
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
    execute (Trunc.submission.image .check) (3 * count + remaining) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) remaining
            (top_checkRootWordsState state start count) allowCoins
          return result.charge (3 * count) 0) := by
  induction count generalizing remaining with
  | zero => simp [top_checkRootWordsState, Execution.charge]
  | succ count ih =>
    have position := top_check_root_words_pc state start location pc count (by omega)
      (fun word bound => agrees word (by omega))
    have scratch : accessValid ((top_checkRootWordsState state start count).getReg .x21 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(top_check_root_words_preserves state start count .x21 (by decide) (by decide)).1]
      exact scratchValid count (by omega)
    have target : accessValid ((top_checkRootWordsState state start count).getReg .x23 +
        BitVec.ofNat 64 (8 * count)) 8 = true := by
      rw [(top_check_root_words_preserves state start count .x23 (by decide) (by decide)).1]
      exact targetValid count (by omega)
    rw [show 3 * (count + 1) + remaining = 3 * count + (3 + remaining) by omega,
      ih (by omega) (fun word bound => agrees word (by omega)),
      top_check_root_word _ start count location (by omega) position scratch target]
    simp [top_checkRootWordsState, Execution.charge, Nat.mul_add, ← Nat.add_assoc]

theorem top_check_root_matches (state : MachineState) (start : Nat)
    (location : start = 294 ∨ start = 394)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (agrees : ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (12 + fuel) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) fuel
            (top_checkRootWordsState state start 4) allowCoins
          return result.charge 12 0) :=
  top_check_root_prefix state start location pc scratchValid targetValid 4 (by decide) agrees fuel allowCoins

theorem top_check_root_first_mismatch (state : MachineState) (start : Nat)
    (location : start = 294 ∨ start = 394)
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
    execute (Trunc.submission.image .check) (3 * word + 6 + fuel) state allowCoins =
      pure ⟨.failure, top_checkExitState (top_checkRootWordState (top_checkRootWordsState state start word) start word) false,
        3 * word + 6, 0⟩ := by
  have prefixPC := top_check_root_words_pc state start location pc word (by omega) earlier
  have scratchReg := (top_check_root_words_preserves state start word .x21 (by decide) (by decide)).1
  have targetPreserves := top_check_root_words_preserves state start word .x23 (by decide) (by decide)
  have targetReg := targetPreserves.1
  have scratchAccess : accessValid ((top_checkRootWordsState state start word).getReg .x21 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [scratchReg]; exact scratchValid word bounded
  have targetAccess : accessValid ((top_checkRootWordsState state start word).getReg .x23 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [targetReg]; exact targetValid word bounded
  have mismatch : (top_checkRootWordsState state start word).getMem
        ((top_checkRootWordsState state start word).getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      (top_checkRootWordsState state start word).getMem
        ((top_checkRootWordsState state start word).getReg .x23 + BitVec.ofNat 64 (8 * word)) := by
    simpa only [scratchReg, targetReg, MachineState.getMem, targetPreserves.2] using different
  rw [Nat.add_assoc, top_check_root_prefix state start location pc scratchValid targetValid word (by omega) earlier,
    top_check_root_word_reject _ start word location bounded prefixPC scratchAccess targetAccess mismatch]
  simp [Execution.charge, Nat.add_comm]

theorem top_check_root_rejects (state : MachineState) (start : Nat)
    (location : start = 294 ∨ start = 394)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : ¬ ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    ∃ result, execute (Trunc.submission.image .check) (15 + fuel) state allowCoins = pure result ∧
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
  refine ⟨⟨.failure, top_checkExitState (top_checkRootWordState (top_checkRootWordsState state start word) start word) false,
    3 * word + 6, 0⟩, ?_, rfl, by dsimp; omega, rfl⟩
  have remaining : 15 + fuel = 3 * word + 6 + (9 - 3 * word + fuel) := by omega
  rw [remaining]
  exact top_check_root_first_mismatch state start location pc scratchValid targetValid word bounded
    earlier mismatch _ allowCoins

theorem top_check_cap_parent_setup (state : MachineState) (pc : state.pc = 5596)
    (fuel : Nat) (allowCoins : Bool) :
    execute (Trunc.submission.image .check) (13 + fuel) state allowCoins =
      (do let result ← execute (Trunc.submission.image .check) fuel
            (checkCapParentSetupState state) allowCoins
          return result.charge 13 0) := by
  apply execute_unit_steps (states := top_capParentSetupPrefix state)
  intro i hi
  refine ⟨.base ((top_capParentSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply sharedFetch _ (375 + i) _ (by unfold untouched; omega)
    · interval_cases i <;>
        simp [top_capParentSetupPrefix, top_capParentSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Trunc.Check
