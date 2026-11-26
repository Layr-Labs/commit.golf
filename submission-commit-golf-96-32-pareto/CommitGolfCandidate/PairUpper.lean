import CommitGolfCandidate.PairPad
namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

def top_checkExitState (state : MachineState) (success : Bool) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 (if success then 0 else 1)).setPC
    (if success then 5628 else 4440)

theorem top_check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 5620 else 4432) (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure, top_checkExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 5624 else 4436)
  have fetch₁ : fetch Late.Check.Normal.checkerImage state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply patchedFetch state 84 _ (by decide) pc; rfl
    · apply patchedFetch state 381 _ (by decide) pc; rfl
  have fetch₂ : fetch Late.Check.Normal.checkerImage next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply patchedFetch next 85 _ (by decide) rfl; rfl
    · apply patchedFetch next 382 _ (by decide) rfl; rfl
  have fetch₃ : fetch Late.Check.Normal.checkerImage (top_checkExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply patchedFetch _ 86 _ (by decide) rfl; rfl
    · apply patchedFetch _ 383 _ (by decide) rfl; rfl
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

def top_checkRootInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x21 (BitVec.ofNat 12 (8 * word)), .LD .x7 .x23 (BitVec.ofNat 12 (8 * word))]

def top_checkRootPrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((top_checkRootInstructions word).take count).foldl execInstrBr state

def top_checkRootBranchOffset (start word : Nat) : BitVec 13 :=
  BitVec.ofNat 13 ((if start = 269 then 7444 else 7044) - 12 * word)

def top_checkRootWordState (state : MachineState) (start word : Nat) : MachineState :=
  execInstrBr (top_checkRootPrefix state word 2) (.BNE .x6 .x7 (top_checkRootBranchOffset start word))

theorem top_check_root_word (state : MachineState) (start word : Nat)
    (location : start = 269 ∨ start = 369) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (3 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel
            (top_checkRootWordState state start word) allowCoins
          return result.charge 3 0) := by
  have loads (remaining : Nat) : execute Late.Check.Normal.checkerImage (2 + remaining) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage remaining
            (top_checkRootPrefix state word 2) allowCoins
          return result.charge 2 0) := by
    apply execute_unit_steps (states := top_checkRootPrefix state word)
    intro i hi
    refine ⟨.base (((top_checkRootInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply patchedFetch _ (start + 3 * word + i) _ (by rcases location with rfl | rfl <;> omega)
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
  have fetched : fetch Late.Check.Normal.checkerImage (top_checkRootPrefix state word 2) =
      some (.base (.BNE .x6 .x7 (top_checkRootBranchOffset start word))) := by
    apply patchedFetch _ (start + 3 * word + 2) _ (by rcases location with rfl | rfl <;> omega)
    · rcases location with rfl | rfl <;> interval_cases word <;>
        simp [top_checkRootPrefix, top_checkRootInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl <;> interval_cases word <;> rfl
  have stepped : ordinaryStep (top_checkRootPrefix state word 2)
      (.base (.BNE .x6 .x7 (top_checkRootBranchOffset start word))) =
        some (top_checkRootWordState state start word) := rfl
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, loads]
  rw [execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

theorem top_check_root_word_preserves (state : MachineState) (start word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (top_checkRootWordState state start word).getReg reg = state.getReg reg ∧
    (top_checkRootWordState state start word).mem = state.mem := by
  constructor
  · simp only [top_checkRootWordState, top_checkRootPrefix, top_checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> simp only [MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLeft),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notRight)]
  · simp only [top_checkRootWordState, top_checkRootPrefix, top_checkRootInstructions, List.take, List.foldl,
      execInstrBr]
    split <;> rfl

theorem top_check_root_word_pc (state : MachineState) (start word : Nat)
    (location : start = 269 ∨ start = 369) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word)) :
    (top_checkRootWordState state start word).pc =
      if state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
          state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) then
        BitVec.ofNat 64 (4096 + 4 * start + 12 * (word + 1)) else 4432 := by
  rcases location with rfl | rfl <;> interval_cases word <;>
    simp [top_checkRootWordState, top_checkRootPrefix, top_checkRootInstructions, top_checkRootBranchOffset,
      execInstrBr, signExtend12, signExtend13, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, MachineState.getMem, pc] <;>
    split <;> simp_all

theorem top_check_root_word_reject (state : MachineState) (start word : Nat)
    (location : start = 269 ∨ start = 369) (bounded : word < 4)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * word))
    (scratchValid : accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (6 + fuel) state allowCoins =
      pure ⟨.failure, top_checkExitState (top_checkRootWordState state start word) false, 6, 0⟩ := by
  have rejectPC : (top_checkRootWordState state start word).pc = 4432 := by
    rw [top_check_root_word_pc state start word location bounded pc, if_neg different]
  rw [show 6 + fuel = 3 + (3 + fuel) by omega,
    top_check_root_word state start word location bounded pc scratchValid targetValid,
    top_check_exit _ false rejectPC]
  simp [Execution.charge]

def top_checkRootWordsState (state : MachineState) (start : Nat) : Nat → MachineState
  | 0 => state
  | count + 1 => top_checkRootWordState (top_checkRootWordsState state start count) start count

theorem top_check_root_words_preserves (state : MachineState) (start count : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (top_checkRootWordsState state start count).getReg reg = state.getReg reg ∧
    (top_checkRootWordsState state start count).mem = state.mem := by
  induction count with
  | zero => exact ⟨rfl, rfl⟩
  | succ count ih =>
    have preserved := top_check_root_word_preserves (top_checkRootWordsState state start count)
      start count reg notLeft notRight
    exact ⟨preserved.1.trans ih.1, preserved.2.trans ih.2⟩

theorem top_check_root_words_read (state : MachineState) (start count word : Nat) (reg : Reg)
    (notLeft : reg ≠ .x6) (notRight : reg ≠ .x7) :
    (top_checkRootWordsState state start count).getMem
        ((top_checkRootWordsState state start count).getReg reg + BitVec.ofNat 64 (8 * word)) =
      state.getMem (state.getReg reg + BitVec.ofNat 64 (8 * word)) := by
  have preserved := top_check_root_words_preserves state start count reg notLeft notRight
  rw [preserved.1]
  exact congrFun preserved.2 _

theorem top_check_root_words_pc (state : MachineState) (start : Nat)
    (location : start = 269 ∨ start = 369)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (count : Nat) (bounded : count ≤ 4)
    (agrees : ∀ word < count,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word))) :
    (top_checkRootWordsState state start count).pc = BitVec.ofNat 64 (4096 + 4 * start + 12 * count) := by
  induction count with
  | zero => exact pc
  | succ count ih =>
    have previous := ih (by omega) (fun word bound => agrees word (by omega))
    rw [top_checkRootWordsState, top_check_root_word_pc _ start count location (by omega) previous,
      top_check_root_words_read state start count count .x21 (by decide) (by decide),
      top_check_root_words_read state start count count .x23 (by decide) (by decide),
      if_pos (agrees count (by omega))]

theorem top_check_root_prefix (state : MachineState) (start : Nat)
    (location : start = 269 ∨ start = 369)
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
    execute Late.Check.Normal.checkerImage (3 * count + remaining) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage remaining
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
    (location : start = 269 ∨ start = 369)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (agrees : ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (12 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel
            (top_checkRootWordsState state start 4) allowCoins
          return result.charge 12 0) :=
  top_check_root_prefix state start location pc scratchValid targetValid 4 (by decide) agrees fuel allowCoins

theorem top_check_root_first_mismatch (state : MachineState) (start : Nat)
    (location : start = 269 ∨ start = 369)
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
    execute Late.Check.Normal.checkerImage (3 * word + 6 + fuel) state allowCoins =
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
    (location : start = 269 ∨ start = 369)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (targetValid : ∀ word < 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : ¬ ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    ∃ result, execute Late.Check.Normal.checkerImage (15 + fuel) state allowCoins = pure result ∧
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

def top_capParentSetupInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
   .ADDI .x10 .x0 0, .SLLI .x10 .x10 11, .ADDI .x10 .x10 4, .SLLI .x10 .x10 11, .ADDI .x10 .x10 448,
   .ADDI .x12 .x0 0, .SLLI .x12 .x12 11, .ADDI .x12 .x12 2, .SLLI .x12 .x12 11, .ADDI .x12 .x12 480]

def top_capParentSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (top_capParentSetupInstructions.take count).foldl execInstrBr state

theorem top_check_cap_parent_setup (state : MachineState) (pc : state.pc = 5496)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (13 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel
            (checkCapParentSetupState state) allowCoins
          return result.charge 13 0) := by
  apply execute_unit_steps (states := top_capParentSetupPrefix state)
  intro i hi
  refine ⟨.base ((top_capParentSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ (350 + i) _ (by omega)
    · interval_cases i <;>
        simp [top_capParentSetupPrefix, top_capParentSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem top_check_cap_parent_setup_registers (state : MachineState) (pc : state.pc = 5496) :
    (checkCapParentSetupState state).pc = 5548 ∧
    (checkCapParentSetupState state).getReg .x5 = 0 ∧
    (checkCapParentSetupState state).getReg .x11 = 64 ∧
    (checkCapParentSetupState state).getReg .x13 = 0 ∧
    (checkCapParentSetupState state).getReg .x10 = 8640 ∧
    (checkCapParentSetupState state).getReg .x12 = 4576 ∧
    (checkCapParentSetupState state).mem = state.mem := by
  rw [show checkCapParentSetupState state = top_capParentSetupPrefix state 13 by rfl]
  dsimp only [checkCapParentSetupState, top_capParentSetupPrefix, top_capParentSetupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12, MachineState.getReg,
    MachineState.setReg, MachineState.setPC]
  simp [pc]

def top_checkCapParentLatchState (state : MachineState) : MachineState :=
  let nextDst := state.getReg .x12 - 32
  ((state.setReg .x10 (state.getReg .x10 - 64)).setReg .x12 nextDst).setPC
    (if nextDst = state.getReg .x22 then 5564 else 5548)

theorem top_check_cap_parent_latch (state : MachineState) (pc : state.pc = 5552)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (3 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel
            (top_checkCapParentLatchState state) allowCoins
          return result.charge 3 0) := by
  let s1 := (state.setReg .x10 (state.getReg .x10 - 64)).setPC 5556
  let s2 := (s1.setReg .x12 (state.getReg .x12 - 32)).setPC 5560
  have f0 : fetch Late.Check.Normal.checkerImage state = some (.base (.ADDI .x10 .x10 4032)) := by
    apply patchedFetch _ 364 _ (by decide) pc; rfl
  have f1 : fetch Late.Check.Normal.checkerImage s1 = some (.base (.ADDI .x12 .x12 4064)) := by
    apply patchedFetch _ 365 _ (by decide) rfl; rfl
  have f2 : fetch Late.Check.Normal.checkerImage s2 = some (.base (.BNE .x12 .x22 8180)) := by
    apply patchedFetch _ 366 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x10 .x10 4032)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc,
      BitVec.sub_eq_add_neg]
  have st1 : ordinaryStep s1 (.base (.ADDI .x12 .x12 4064)) = some s2 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, s2,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have st2 : ordinaryStep s2 (.base (.BNE .x12 .x22 8180)) = some (top_checkCapParentLatchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, s1, s2,
      top_checkCapParentLatchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, st0, f1, st1, f2, st2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def top_checkCapParentStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  top_checkCapParentLatchState (paddedCompressionState state answer)

theorem top_cap_parent_step_registers (state : MachineState) (answer : BitVec 256) :
    (top_checkCapParentStepState state answer).getReg .x10 = state.getReg .x10 - 64 ∧
    (top_checkCapParentStepState state answer).getReg .x12 = state.getReg .x12 - 32 ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      (top_checkCapParentStepState state answer).getReg reg = state.getReg reg := by
  have padReg (r : Reg) (n11 : r ≠ .x11) (n14 : r ≠ .x14) (n15 : r ≠ .x15)
      (n16 : r ≠ .x16) (n17 : r ≠ .x17) (n31 : r ≠ .x31) :
      (paddedCompressionState state answer).getReg r = state.getReg r :=
    padded_compression_register state answer r n14 n15 n16 n17 n31 n11
  refine ⟨?_, ?_, ?_⟩
  · simp only [top_checkCapParentStepState, top_checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      padReg .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [top_checkCapParentStepState, top_checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      padReg .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rcases hr with ⟨n10, n11, n12, n14, n15, n16, n17, n31⟩
    simp only [top_checkCapParentStepState, top_checkCapParentLatchState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n12),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n10)]
    exact padReg reg n11 n14 n15 n16 n17 n31

theorem top_cap_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (top_checkCapParentStepState state answer).pc =
      if state.getReg .x12 - 32 = state.getReg .x22 then 5564 else 5548 := by
  change (if (paddedCompressionState state answer).getReg .x12 - 32 =
      (paddedCompressionState state answer).getReg .x22 then 5564 else 5548) = _
  rw [padded_compression_register state answer .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    padded_compression_register state answer .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

def top_checkCapParentLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))
      top_checkCapParentLoop (top_checkCapParentStepState state answer) count

theorem top_check_cap_parent_loop (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (pc : 0 < count → state.pc = 5548)
    (r5 : state.getReg .x5 = 0) (r13 : state.getReg .x13 = 0)
    (r22 : state.getReg .x22 = 512)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (20 * count + fuel) state allowCoins =
      (do let finished ← top_checkCapParentLoop state count
          let result ← execute Late.Check.Normal.checkerImage fuel finished allowCoins
          return result.charge (27 * count) count) := by
  induction count generalizing state with
  | zero => simp [top_checkCapParentLoop, Execution.charge]
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have r12Nat : (state.getReg .x12).toNat = 512 + 32 * (count + 1) := by
      rw [r12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have srcValid : rangeValid (state.getReg .x10) 96 = true := by
      simp only [rangeValid, r10Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have dstValid : rangeValid (state.getReg .x12) 32 = true := by
      simp only [rangeValid, r12Nat, MEMORY_BYTES, decide_eq_true_eq]; omega
    have call := rec_padding_call true state 363 (Or.inr rfl) (pc (by omega))
      r5 r13 srcValid dstValid (by rw [r10Nat]; omega) (by rw [r12Nat]; omega)
      (by rw [r10Nat, r12Nat]; omega) (3 + (20 * count + fuel)) allowCoins
    rw [show 20 * (count + 1) + fuel = 17 + (3 + (20 * count + fuel)) by omega]
    erw [call]
    simp only [top_checkCapParentLoop, bind_assoc, pure_bind]
    apply congrArg (fun k =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer state (state.getReg .x10).toNat 64))))) :
        OracleComp World (BitVec 256)) >>= k)
    funext answer
    change BitVec 256 at answer
    have afterPC : (paddedCompressionState state answer).pc = 5552 := by
      rw [padded_compression_pc, pc (by omega)]; rfl
    have next10 : (top_checkCapParentStepState state answer).getReg .x10 =
        BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(top_cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : (top_checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextPC : 0 < count → (top_checkCapParentStepState state answer).pc = 5548 := by
      intro pos
      rw [top_cap_parent_step_pc, ← (top_cap_parent_step_registers state answer).2.1, next12, r22, if_neg]
      intro eq
      have n := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 512 + 32 * count < 2^64)] at n
      change 512 + 32 * count = 512 at n
      omega
    have stepDef : top_checkCapParentLatchState (paddedCompressionState state answer) =
        top_checkCapParentStepState state answer := rfl
    rw [top_check_cap_parent_latch _ afterPC, stepDef,
      ih (by omega) (top_checkCapParentStepState state answer) nextPC
        (((top_cap_parent_step_registers state answer).2.2 .x5 (by decide)).trans r5)
        (((top_cap_parent_step_registers state answer).2.2 .x13 (by decide)).trans r13)
        (((top_cap_parent_step_registers state answer).2.2 .x22 (by decide)).trans r22)
        next10 next12]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro finished
    apply bind_congr
    intro res
    congr 1
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    constructor <;> omega

theorem top_cap_parent_loop_finished (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r22 : state.getReg .x22 = 512)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (top_checkCapParentLoop state count)) :
    (0 < count → finished.pc = 5564) ∧
    ∀ reg ∉ [Reg.x10, .x11, .x12, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [top_checkCapParentLoop, support_pure, Set.mem_singleton_iff] at reached
    subst finished
    exact ⟨by omega, fun _ _ => rfl⟩
  | succ count ih =>
    simp only [top_checkCapParentLoop, mem_support_bind_iff] at reached
    obtain ⟨answer, _, tailReached⟩ := reached
    change BitVec 256 at answer
    have next12 : (top_checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next22 : (top_checkCapParentStepState state answer).getReg .x22 = 512 :=
      ((top_cap_parent_step_registers state answer).2.2 .x22 (by decide)).trans r22
    have rest := ih (by omega) _ next22 next12 tailReached
    refine ⟨?_, ?_⟩
    · intro _
      cases count with
      | zero =>
        simp only [top_checkCapParentLoop, support_pure, Set.mem_singleton_iff] at tailReached
        subst finished
        rw [top_cap_parent_step_pc, ← (top_cap_parent_step_registers state answer).2.1, next12, r22]
        rfl
      | succ count => exact rest.1 (by omega)
    · intro reg hr
      exact (rest.2 reg hr).trans ((top_cap_parent_step_registers state answer).2.2 reg hr)

theorem top_align_to_dword_of_nat (n : Nat) (hn : n < 2 ^ 64) :
    alignToDword (BitVec.ofNat 64 n) = BitVec.ofNat 64 (8 * (n / 8)) := by
  have offset : byteOffset (BitVec.ofNat 64 n) = n % 8 := by
    unfold byteOffset
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    change n &&& (2 ^ 3 - 1) = n % 2 ^ 3
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have parts : alignToDword (BitVec.ofNat 64 n) + BitVec.ofNat 64 (byteOffset (BitVec.ofNat 64 n)) =
      BitVec.ofNat 64 n := by
    unfold alignToDword byteOffset
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have disjoint : (BitVec.ofNat 64 n &&& ~~~7#64) &&& (BitVec.ofNat 64 n &&& 7#64) = 0 := by
      ext i; simp only [BitVec.getElem_and, BitVec.getElem_not]; cases (7#64)[i] <;> simp
    have combined : (BitVec.ofNat 64 n &&& ~~~7#64) ||| (BitVec.ofNat 64 n &&& 7#64) =
        BitVec.ofNat 64 n := by
      ext i; simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]; cases (7#64)[i] <;> simp
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]
  rw [offset] at parts
  have joined : BitVec.ofNat 64 (8 * (n / 8)) + BitVec.ofNat 64 (n % 8) = BitVec.ofNat 64 n := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  have canceled := congrArg (fun value : Word => value - BitVec.ofNat 64 (n % 8)) (parts.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using canceled

theorem top_cap_parent_loop_support_outside (count : Nat) (bounded : count ≤ 127) (state : MachineState)
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (finished : MachineState) (reached : finished ∈ support (top_checkCapParentLoop state count))
    (address : Word)
    (outside : address.toNat < 544 ∨ 512 + 32 * (count + 1) ≤ address.toNat) :
    finished.getMem address = state.getMem address := by
  induction count generalizing state with
  | zero =>
    simp only [top_checkCapParentLoop, support_pure, Set.mem_singleton_iff] at reached
    subst finished; rfl
  | succ count ih =>
    simp only [top_checkCapParentLoop, mem_support_bind_iff] at reached
    obtain ⟨answer, _, tailReached⟩ := reached
    change BitVec 256 at answer
    have next12 : (top_checkCapParentStepState state answer).getReg .x12 =
        BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    rw [ih (by omega) _ next12 tailReached (by omega)]
    change (paddedCompressionState state answer).mem address = state.mem address
    rw [padded_compression_memory state answer]
    apply writeBits_memory_outside
    intro i hi
    change i < 32 at hi
    rw [r12]
    intro eq
    have addEq : BitVec.ofNat 64 (512 + 32 * (count + 1)) + BitVec.ofNat 64 i =
        BitVec.ofNat 64 (512 + 32 * (count + 1) + i) := (BitVec.ofNat_add _ _).symm
    rw [addEq, top_align_to_dword_of_nat _ (by omega)] at eq
    have same := congrArg BitVec.toNat eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at same
    omega

def top_checkCapRootSetupState (state : MachineState) : MachineState :=
  ((state.setReg .x21 (state.getReg .x22 + 32)).setReg .x23 (state.getReg .x26)).setPC 5572

theorem top_check_cap_root_setup (state : MachineState) (pc : state.pc = 5564)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (2 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel
            (top_checkCapRootSetupState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x21 (state.getReg .x22 + 32)).setPC 5568
  have f0 : fetch Late.Check.Normal.checkerImage state = some (.base (.ADDI .x21 .x22 32)) := by
    apply patchedFetch _ 367 _ (by decide) pc; rfl
  have f1 : fetch Late.Check.Normal.checkerImage s1 = some (.base (.ADDI .x23 .x26 0)) := by
    apply patchedFetch _ 368 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.ADDI .x21 .x22 32)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADDI .x23 .x26 0)) = some (top_checkCapRootSetupState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, s1,
      top_checkCapRootSetupState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem top_cap_parent_step_mem (state : MachineState) (answer : BitVec 256) :
    (top_checkCapParentStepState state answer).mem = (paddedCompressionState state answer).mem := rfl

theorem top_cap_parent_loop_heap (oracle : Oracle) (state : MachineState)
    (cap : Nat → Digest) (count : Nat) (bounded : count ≤ 127)
    (r10 : state.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count))
    (r12 : state.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count))
    (above : ∀ slot, count < slot → slot < 256 →
      readBuffer state (512 + 32 * slot) 32 = referenceHeap oracle.compression 128 cap slot) :
    ∀ slot, 0 < slot → slot < 256 →
      readBuffer (Late.Check.Normal.checkEvaluation oracle (top_checkCapParentLoop state count)).1 (512 + 32 * slot) 32 =
        referenceHeap oracle.compression 128 cap slot := by
  induction count generalizing state with
  | zero =>
    intro slot pos hi
    rw [top_checkCapParentLoop, Late.Check.Normal.check_evaluation_pure]
    exact above slot pos hi
  | succ count ih =>
    have r10Nat : (state.getReg .x10).toNat = 512 + 64 * (count + 1) := by
      rw [r10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h64 : readBuffer state (state.getReg .x10).toNat 64 =
        referenceHeap oracle.compression 128 cap (2 * (count + 1) + 1) ++
          referenceHeap oracle.compression 128 cap (2 * (count + 1)) := by
      rw [r10Nat, read_compression_halves state _ (by omega)]
      have leftAddr : 512 + 64 * (count + 1) = 512 + 32 * (2 * (count + 1)) := by omega
      have rightAddr : 512 + 64 * (count + 1) + 32 = 512 + 32 * (2 * (count + 1) + 1) := by omega
      rw [rightAddr, leftAddr,
        above (2 * (count + 1) + 1) (by omega) (by omega),
        above (2 * (count + 1)) (by omega) (by omega)]
    let answer : BitVec 256 := oracle.compression (padInput (readBuffer state (state.getReg .x10).toNat 64))
    have answerEq : answer = referenceHeap oracle.compression 128 cap (count + 1) := by
      dsimp only [answer]
      rw [h64]
      exact (reference_heap_parent oracle.compression 128 cap (count + 1) (by omega) (by omega)).symm
    let next := top_checkCapParentStepState state answer
    have next10 : next.getReg .x10 = BitVec.ofNat 64 (512 + 64 * count) := by
      rw [(top_cap_parent_step_registers state answer).1, r10]
      change BitVec.ofNat 64 (512 + 64 * (count + 1)) - BitVec.ofNat 64 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have next12 : next.getReg .x12 = BitVec.ofNat 64 (512 + 32 * count) := by
      rw [(top_cap_parent_step_registers state answer).2.1, r12]
      change BitVec.ofNat 64 (512 + 32 * (count + 1)) - BitVec.ofNat 64 32 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by omega) (by omega)]
      congr 1
    have nextMem : next.mem = (writeBits state (BitVec.ofNat 64 (512 + 32 * (count + 1))) answer).mem := by
      dsimp only [next]
      rw [top_cap_parent_step_mem, padded_compression_memory state answer, r12]
    have nextAbove (slot : Nat) (lo : count < slot) (hi : slot < 256) :
        readBuffer next (512 + 32 * slot) 32 = referenceHeap oracle.compression 128 cap slot := by
      rw [read_buffer_memory_congr _ _ nextMem]
      by_cases eq : slot = count + 1
      · subst slot
        have w := write_bits_digest (bits := 256) state (512 + 32 * (count + 1)) 0 answer (by decide) (by decide)
        rw [← answerEq]
        exact w.trans (by
          apply BitVec.eq_of_getLsbD_eq
          intro i hi
          rw [BitVec.getLsbD_extractLsb']
          simp [hi])
      · have preserved := write_bits_read_outside (bits := 256) state answer (512 + 32 * (count + 1))
          (512 + 32 * slot) 32 (by omega) (by omega) (Or.inr (by omega))
        exact preserved.trans (above slot (by omega) hi)
    intro slot pos hi
    rw [top_checkCapParentLoop, Late.Check.Normal.check_evaluation_public_bind]
    exact ih next (by omega) next10 next12 nextAbove slot pos hi

end CommitGolfCandidate.PairCap
