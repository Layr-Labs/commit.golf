import CommitGolfCandidate.CheckRefinement

/-! Exact acceptance behavior of the checker image. Every requested position must
reconstruct the supplied root; a failed comparison rejects the whole opening. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The four comparisons made by the root-comparison block. -/
def rootWordsMatch (state : MachineState) : Bool :=
  decide (∀ word : Fin 4,
    state.getMem (state.getReg .x21+BitVec.ofNat 64 (8*word.val)) =
      state.getMem (state.getReg .x26+BitVec.ofNat 64 (8*word.val)))

theorem root_words_match_iff (state : MachineState) :
    rootWordsMatch state = true ↔
      ∀ word < 4, state.getMem (state.getReg .x21+BitVec.ofNat 64 (8*word)) =
        state.getMem (state.getReg .x26+BitVec.ofNat 64 (8*word)) := by
  simp only [rootWordsMatch, decide_eq_true_eq]
  exact ⟨fun h word bound => h ⟨word, bound⟩, fun h word => h word word.isLt⟩

/-- A finite, deterministic description of the machine's outer loop. Its hash state
is the actual machine computation whose digest is characterized in CheckRefinement. -/
def checkLoopAccepts (oracle : Oracle) : Nat → MachineState → Bool
  | 0, _ => true
  | count+1, state =>
      let hashed := (checkEvaluation oracle (checkPositionHash state)).1
      rootWordsMatch hashed &&
        checkLoopAccepts oracle count (checkPositionNextState (checkRootWordsState hashed 4))

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
  execute pathInstructions checkEvaluation checkLoopAccepts

set_option maxHeartbeats 500000 in
/-- The real checker accepts exactly when every iteration passes its root comparison.
This includes malformed proof contents and every fixed oracle realization. -/
theorem check_loop_acceptance (oracle : Oracle) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2^24) (invariant : CheckLoopInvariant state count) (fuel : Nat) :
    (checkEvaluation oracle
      (execute (submission.image .check) (1412*count+3+fuel) state false)).1.exit = .success ↔
        checkLoopAccepts oracle count state = true := by
  induction count generalizing state fuel with
  | zero =>
    have pc : state.pc = 4420 := by simpa using invariant.pc
    rw [show 1412*0+3+fuel = 3+fuel by omega, check_exit state true pc,
      check_evaluation_pure, checkLoopAccepts]
    simp
  | succ count ih =>
    have pc : state.pc = 4152 := by simpa using invariant.pc
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simpa using invariant.indices 0 (by omega)
    have proofValid : ∀ word < 100,
        accessValid (state.getReg .x25+BitVec.ofNat 64 (8*word)) 8 = true :=
      fun word smaller => invariant.proofs word (by omega)
    have valueValid : ∀ word < 32,
        accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true :=
      fun word smaller => invariant.values word (by omega)
    let steps := pathInstructions (state.getMem (state.getReg .x24)) 24
    have stepBound : steps ≤ 1080 := (path_instruction_bounds _ 24).2
    let extra := fuel+(1116-steps)
    let hashed := (checkEvaluation oracle (checkPositionHash state)).1
    have reached : hashed ∈ support (checkPositionHash state) := check_evaluation_support oracle _
    have regs := check_position_hash_registers state hashed reached
    have scratchValid : ∀ word < 4,
        accessValid (hashed.getReg .x21+BitVec.ofNat 64 (8*word)) 8 = true := by
      rw [regs.2.2.2 .x21 (by simp), invariant.scratch]
      intro word smaller
      interval_cases word <;> decide
    have rootValid : ∀ word < 4,
        accessValid (hashed.getReg .x26+BitVec.ofNat 64 (8*word)) 8 = true := by
      rw [regs.2.2.2 .x26 (by simp)]
      exact invariant.root
    have budget : 1412*(count+1)+3+fuel = 281+steps+(15+(1412*count+3+extra)) := by
      dsimp [extra]
      omega
    rw [budget, check_position_hash state pc indexValid invariant.scratch proofValid valueValid,
      evaluation_hash_exit]
    change (checkEvaluation oracle (execute (submission.image .check)
      (15+(1412*count+3+extra)) hashed false)).1.exit = .success ↔ _
    by_cases agrees : rootWordsMatch hashed = true
    · have words := (root_words_match_iff hashed).mp agrees
      have comparedPC : (checkRootWordsState hashed 4).pc = 4408 :=
        check_root_words_pc hashed regs.1 4 (by decide) words
      have nextInvariant := check_loop_next_invariant state hashed count (by omega) invariant reached
      rw [show 15+(1412*count+3+extra) = 12+(3+(1412*count+3+extra)) by omega,
        check_root_matches hashed regs.1 scratchValid rootValid words,
        evaluation_charge_exit, check_position_next _ comparedPC, evaluation_charge_exit]
      rw [ih _ (by omega) nextInvariant extra]
      simp only [checkLoopAccepts, hashed, agrees, Bool.true_and]
    · have words : ¬ ∀ word < 4,
          hashed.getMem (hashed.getReg .x21+BitVec.ofNat 64 (8*word)) =
            hashed.getMem (hashed.getReg .x26+BitVec.ofNat 64 (8*word)) :=
        fun h => agrees ((root_words_match_iff hashed).mpr h)
      obtain ⟨failed, run, exit, _, _⟩ := check_root_rejects hashed regs.1 scratchValid rootValid
        words (1412*count+3+extra) false
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

/-- Exact acceptance through the trusted ABI: the proof length must be 800 bytes per
requested leaf, and every requested leaf must pass its root comparison. -/
theorem check_input_acceptance (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (submission.run .check input)).1.exit = .success ↔
      input.proof.length = 800*input.positions.card ∧
        checkLoopAccepts oracle input.positions.card
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  have cardinal : input.positions.card ≤ 2^24 := by
    have bound : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bound
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · by_cases rightLength : input.proof.length = 800*input.positions.card
    · let initial := submission.initialState .check input
      have lengthPC : (checkLengthState initial).pc = 4136 :=
        if_pos ((check_input_length input valid).mpr rightLength)
      let extra := submission.steps .check-(1412*input.positions.card+17)
      have budget : submission.steps .check = 10+(4+(1412*input.positions.card+3+extra)) := by
        change 214748365824 = 10+(4+(1412*input.positions.card+3+
          (214748365824-(1412*input.positions.card+17))))
        omega
      rw [run_check_valid input valid, budget, check_length_gate initial rfl,
        evaluation_charge_exit, check_ready _ lengthPC, evaluation_charge_exit,
        check_loop_acceptance oracle _ input.positions.card cardinal (check_input_invariant input) extra]
      simp only [rightLength, true_and]
    · rw [check_input_wrong_length input valid rightLength, check_evaluation_pure]
      simp only [rightLength, false_and]
      decide
  · have notLength : input.proof.length ≠ 800*input.positions.card := by
      change ¬ input.proof.length ≤ 13421772800 at valid
      omega
    rw [check_oversized input (by omega), check_evaluation_pure]
    simp only [notLength, false_and]
    decide

/-- The security-game scheme uses this same acceptance condition, not an abstract
checker substituted for the submitted program. -/
theorem scheme_check_acceptance (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true ↔
      input.proof.length = 800*input.positions.card ∧
        checkLoopAccepts oracle input.positions.card
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  rw [scheme_check_evaluation]
  simp only [beq_iff_eq]
  exact check_input_acceptance oracle input

end CommitGolfCandidate
