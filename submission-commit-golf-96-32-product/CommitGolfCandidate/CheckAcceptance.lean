import CommitGolfCandidate.CheckRefinement
import CommitGolfCandidate.CheckCapRefinement

/-! Exact acceptance behavior of the checker image, covering both normal openings
(`k ≠ 128`, depth 24) and level-7 cap-table openings (`k = 128`, depth 17). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The four comparisons made by both digest-comparison blocks (`check-root` and `cap-root`):
`[x21, x21 + 32)` vs `[x23, x23 + 32)`. -/
def rootWordsMatch (state : MachineState) : Bool :=
  decide (∀ word : Fin 4,
    state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) =
      state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)))

theorem root_words_match_iff (state : MachineState) :
    rootWordsMatch state = true ↔
      ∀ word < 4, state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x23 + BitVec.ofNat 64 (8 * word)) := by
  simp only [rootWordsMatch, decide_eq_true_eq]
  exact ⟨fun h word bound => h ⟨word, bound⟩, fun h word => h word word.isLt⟩

/-- A finite, deterministic description of the machine's unified outer loop at depth
`pathDepth` (`24` in normal mode, `17` in cap mode). -/
def checkLoopAccepts (oracle : Oracle) : Nat → Nat → MachineState → Bool
  | 0, _, _ => true
  | count + 1, pathDepth, state =>
      let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
      rootWordsMatch hashed &&
        checkLoopAccepts oracle count pathDepth
          (checkPositionNextState (checkRootWordsState hashed 66 4))

private theorem evaluation_charge_exit (oracle : Oracle) (computation : OracleComp World Execution)
    (cycles calls : Nat) :
    (checkEvaluation oracle (do let result ← computation; return result.charge cycles calls)).1.exit =
      (checkEvaluation oracle computation).1.exit := by
  rw [check_evaluation_bind]
  simp only [check_evaluation_pure, Execution.charge]

private theorem evaluation_hash_exit (oracle : Oracle) (hash : OracleComp World MachineState)
    (continuation : MachineState → OracleComp World Execution) (cycles calls : Nat) :
    (checkEvaluation oracle (do
      let state ← hash
      let result ← continuation state
      return result.charge cycles calls)).1.exit =
      (checkEvaluation oracle (continuation (checkEvaluation oracle hash).1)).1.exit := by
  rw [check_evaluation_bind, evaluation_charge_exit]

attribute [local irreducible] checkRootWordsState checkPositionNextState checkPositionHash
  checkCapHash execute pathInstructions checkEvaluation checkLoopAccepts

set_option maxHeartbeats 600000 in
/-- The real checker outer loop accepts iff every iteration passes its target comparison. -/
theorem check_loop_acceptance (oracle : Oracle) (state : MachineState) (count pathDepth : Nat)
    (bounded : count ≤ 2 ^ 24) (invariant : CheckLoopInvariant state count pathDepth) (fuel : Nat) :
    (checkEvaluation oracle
      (execute (submission.image .check) (1412 * count + 3 + fuel) state false)).1.exit = .success ↔
        checkLoopAccepts oracle count pathDepth state = true := by
  induction count generalizing state fuel with
  | zero =>
    have pc : state.pc = 4420 := by simpa using invariant.pc
    rw [show 1412 * 0 + 3 + fuel = 3 + fuel by omega, check_exit state true pc,
      check_evaluation_pure, checkLoopAccepts]
    simp
  | succ count ih =>
    have pc : state.pc = 4156 := by simpa using invariant.pc
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simpa using invariant.indices 0 (by omega)
    have indexSmall : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using invariant.indexValues 0 (by omega)
    have proofValid : ∀ word < 2 + 4 * pathDepth,
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.proofs word (by
        have : (2 + 4 * pathDepth) * 1 ≤ (2 + 4 * pathDepth) * (count + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega)
    have valueValid : ∀ word < 32,
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.values word (by omega)
    let steps := pathInstructions (state.getMem (state.getReg .x24)) pathDepth
    have stepBound : steps ≤ 45 * pathDepth := (path_instruction_bounds _ pathDepth).2
    have depthLe : pathDepth ≤ 24 := invariant.depthBound
    let extra := fuel + (1281 - steps)
    let hashed := (checkEvaluation oracle (checkPositionHash state pathDepth)).1
    have reached : hashed ∈ support (checkPositionHash state pathDepth) :=
      check_evaluation_support oracle _
    have regs := check_position_hash_registers pathDepth invariant.depthPos invariant.depthBound
      state hashed invariant.depthReg reached
    have scratchValid : ∀ word < 4,
        accessValid (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [regs.2.2.2.2 .x21 (by simp), invariant.scratch]
      intro word smaller
      interval_cases word <;> decide
    have targetValid : ∀ word < 4,
        accessValid (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [regs.2.2.2.1]
      exact check_target_access_valid pathDepth invariant.depthBound _ _ indexSmall invariant.targets
    have budget : 1412 * (count + 1) + 3 + fuel = 116 + steps + (15 + (1412 * count + 3 + extra)) := by
      dsimp [extra]
      omega
    rw [budget, check_position_hash pathDepth invariant.depthPos invariant.depthBound state pc
      invariant.depthReg indexValid invariant.scratch proofValid valueValid,
      evaluation_hash_exit]
    change (checkEvaluation oracle (execute (submission.image .check)
      (15 + (1412 * count + 3 + extra)) hashed false)).1.exit = .success ↔ _
    by_cases agrees : rootWordsMatch hashed = true
    · have words := (root_words_match_iff hashed).mp agrees
      have comparedPC : (checkRootWordsState hashed 66 4).pc = 4408 :=
        check_root_words_pc hashed 66 (Or.inl rfl) regs.1 4 (by decide) words
      have nextInvariant := check_loop_next_invariant state hashed count pathDepth (by omega)
        invariant reached
      rw [show 15 + (1412 * count + 3 + extra) = 12 + (3 + (1412 * count + 3 + extra)) by omega,
        check_root_matches hashed 66 (Or.inl rfl) regs.1 scratchValid targetValid words,
        evaluation_charge_exit, check_position_next _ comparedPC, evaluation_charge_exit]
      rw [ih _ (by omega) nextInvariant extra]
      simp only [checkLoopAccepts, hashed, agrees, Bool.true_and]
    · have words : ¬ ∀ word < 4,
          hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
            hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) :=
        fun h => agrees ((root_words_match_iff hashed).mpr h)
      obtain ⟨failed, run, exit, _, _⟩ := check_root_rejects hashed 66 (Or.inl rfl) regs.1
        scratchValid targetValid words (1412 * count + 3 + extra) false
      rw [run, check_evaluation_pure, exit]
      have mismatch : rootWordsMatch hashed = false := Bool.eq_false_iff.mpr agrees
      simp only [checkLoopAccepts, hashed, mismatch, Bool.false_and, Bool.false_eq_true]
      decide

private theorem run_check_valid (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) :
    submission.run .check input = execute (submission.image .check) (submission.steps .check)
      (submission.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]
  rfl

private theorem cap_commit_access (word : Nat) (hw : word < 4) :
    accessValid (BitVec.ofNat 64 4294971392 + BitVec.ofNat 64 (8 * word)) 8 = true := by
  interval_cases word <;> decide

set_option maxHeartbeats 600000 in
/-- Exact acceptance through the trusted ABI for both normal (`k ≠ 128`) and cap-table
(`k = 128`) openings. -/
theorem check_input_acceptance (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (submission.run .check input)).1.exit = .success ↔
      if input.positions.card = BATCH then
        input.proof.length = 75776 ∧
        let hashed := (checkEvaluation oracle (checkCapHash (submission.initialState .check input))).1
        rootWordsMatch hashed = true ∧
        checkLoopAccepts oracle BATCH 17 (checkCapEnterLoopState (checkRootWordsState hashed 138 4)) = true
      else
        input.proof.length = 784 * input.positions.card ∧
        checkLoopAccepts oracle input.positions.card 24
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  have cardinal : input.positions.card ≤ 2 ^ 24 := by
    have bound : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bound
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · by_cases batch : input.positions.card = BATCH
    · rw [if_pos batch]
      by_cases rightLen : input.proof.length = 75776
      · let initial := submission.initialState .check input
        have is128 : initial.getReg .x16 = 128 := by
          change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
        have isLen : initial.getReg .x17 = 75776 := by
          change BitVec.ofNat 64 input.proof.length = 75776; rw [rightLen]; rfl
        let hashed := (checkEvaluation oracle (checkCapHash initial)).1
        have reached : hashed ∈ support (checkCapHash initial) := check_evaluation_support oracle _
        have hRegs := check_cap_hash_registers initial hashed is128 isLen reached
        have scratchValid : ∀ word < 4,
            accessValid (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true := by
          rw [hRegs.2.1]; intro word hw; interval_cases word <;> decide
        have targetValid : ∀ word < 4,
            accessValid (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true := by
          rw [hRegs.2.2.1]; exact cap_commit_access
        let extra := submission.steps .check - (4118 + 15 + 4 + (1412 * BATCH + 3))
        have hsteps : submission.steps .check = 214748365824 := rfl
        have budget : submission.steps .check =
            4118 + (15 + (4 + (1412 * BATCH + 3 + extra))) := by
          dsimp [extra]; rw [hsteps]; decide
        rw [run_check_valid input valid, budget,
          check_cap_hash initial rfl is128 isLen rfl, evaluation_hash_exit]
        change (checkEvaluation oracle (execute (submission.image .check)
          (15 + (4 + (1412 * BATCH + 3 + extra))) hashed false)).1.exit = .success ↔ _
        by_cases agrees : rootWordsMatch hashed = true
        · have words := (root_words_match_iff hashed).mp agrees
          have compPC : (checkRootWordsState hashed 138 4).pc = 4696 :=
            check_root_words_pc hashed 138 (Or.inr rfl) hRegs.1 4 (by decide) words
          have inv := check_cap_loop_invariant input hashed batch rightLen reached
          rw [show 15 + (4 + (1412 * BATCH + 3 + extra)) =
              12 + (4 + (1412 * BATCH + 3 + (extra + 3))) by omega,
            check_root_matches hashed 138 (Or.inr rfl) hRegs.1 scratchValid targetValid words,
            evaluation_charge_exit, check_cap_enter_loop _ compPC, evaluation_charge_exit,
            check_loop_acceptance oracle _ BATCH 17 (by decide) inv (extra + 3)]
          dsimp only [hashed, initial] at agrees ⊢
          simp only [rightLen, agrees, true_and]
        · have words : ¬ ∀ word < 4,
              hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
                hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) :=
            fun h => agrees ((root_words_match_iff hashed).mpr h)
          obtain ⟨failed, run, exit, _, _⟩ := check_root_rejects hashed 138 (Or.inr rfl) hRegs.1
            scratchValid targetValid words (4 + (1412 * BATCH + 3 + extra)) false
          rw [run, check_evaluation_pure, exit]
          dsimp only [hashed, initial] at agrees ⊢
          simp only [rightLen, agrees, Bool.false_eq_true, false_and, true_and, iff_false]
          decide
      · rw [check_input_cap_wrong_length input valid batch rightLen, check_evaluation_pure]
        simp only [rightLen, false_and]
        decide
    · rw [if_neg batch]
      by_cases rightLength : input.proof.length = 784 * input.positions.card
      · let initial := submission.initialState .check input
        have not128 : initial.getReg .x16 ≠ 128 := by
          intro h; have n := congrArg BitVec.toNat h
          change input.positions.card % 2 ^ 64 = 128 at n
          rw [Nat.mod_eq_of_lt (by omega)] at n; exact batch n
        have lengthPC : (checkLengthState initial).pc = 4144 :=
          if_pos ((check_input_length input valid).mpr rightLength)
        let extra := submission.steps .check - (1412 * input.positions.card + 18)
        have budget : submission.steps .check = 12 + (3 + (1412 * input.positions.card + 3 + extra)) := by
          change 214748365824 = 12 + (3 + (1412 * input.positions.card + 3 +
            (214748365824 - (1412 * input.positions.card + 18))))
          omega
        rw [run_check_valid input valid, budget, check_length_gate initial rfl not128,
          evaluation_charge_exit, check_ready _ lengthPC, evaluation_charge_exit,
          check_loop_acceptance oracle _ input.positions.card 24 cardinal (check_input_invariant input) extra]
        simp only [rightLength, true_and]
      · rw [check_input_wrong_length input valid batch rightLength, check_evaluation_pure]
        simp only [rightLength, false_and]
        decide
  · rw [check_oversized input (by omega), check_evaluation_pure]
    change ¬ input.proof.length ≤ 13153337344 at valid
    by_cases batch : input.positions.card = BATCH
    · rw [if_pos batch]
      have notLen : input.proof.length ≠ 75776 := by omega
      simp only [notLen, false_and]
      decide
    · rw [if_neg batch]
      have notLen : input.proof.length ≠ 784 * input.positions.card := by omega
      simp only [notLen, false_and]
      decide

/-- The security-game scheme uses this same acceptance condition, not an abstract
checker substituted for the submitted program. -/
theorem scheme_check_acceptance (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true ↔
      if input.positions.card = BATCH then
        input.proof.length = 75776 ∧
        let hashed := (checkEvaluation oracle (checkCapHash (submission.initialState .check input))).1
        rootWordsMatch hashed = true ∧
        checkLoopAccepts oracle BATCH 17 (checkCapEnterLoopState (checkRootWordsState hashed 138 4)) = true
      else
        input.proof.length = 784 * input.positions.card ∧
        checkLoopAccepts oracle input.positions.card 24
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  rw [scheme_check_evaluation]
  simp only [beq_iff_eq]
  exact check_input_acceptance oracle input

end CommitGolfCandidate
