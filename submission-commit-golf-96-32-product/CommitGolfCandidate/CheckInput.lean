import CommitGolfCandidate.CheckLoop
import CommitGolfCandidate.CheckCap
import CommitGolfCandidate.Counting
import CommitGolfCandidate.InputOrder

/-! Discharge the checker loop's invariants using the trusted input ABI, covering both
normal openings (`k ≠ 128`, depth 24) and cap-table openings (`k = 128`, depth 17). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem check_buffer_access (base words word : Nat)
    (space : base + 8 * words ≤ MEMORY_BYTES) (aligned : base % 8 = 0) (inside : word < words) :
    accessValid (BitVec.ofNat 64 base + BitVec.ofNat 64 (8 * word)) 8 = true := by
  have baseSmall : base < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  have offsetSmall : 8 * word < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  have totalSmall : base + 8 * word < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  simp only [accessValid, rangeValid, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt baseSmall, Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt totalSmall,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

private theorem index_outside_scratch (word i : Nat) (hw : word < 2 ^ 24) (hi : i < 12) :
    BitVec.ofNat 64 6442455072 + BitVec.ofNat 64 (8 * word) ≠ BitVec.ofNat 64 (256 + 8 * i) := by
  intro eq
  have n := congrArg BitVec.toNat eq
  rw [← BitVec.ofNat_add] at n
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 6442455072 + 8 * word < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 256 + 8 * i < 2 ^ 64)] at n
  omega

private theorem initial_index_bound (input : CheckInput) (word : Nat)
    (inside : word < input.positions.card) :
    ((submission.initialState .check input).getMem
      (BitVec.ofNat 64 6442455072 + BitVec.ofNat 64 (8 * word))).toNat < 2 ^ 24 := by
  have eqAddr : BitVec.ofNat 64 6442455072 + BitVec.ofNat 64 (8 * word) =
      BitVec.ofNat 64 (submission.layout.indices + 8 * word) := (BitVec.ofNat_add _ _).symm
  rw [eqAddr, check_input_position input word inside, BitVec.toNat_ofNat]
  have lt24 : openingIndex input.positions word < 2 ^ 24 :=
    opening_index_bound input.positions word
  rw [Nat.mod_eq_of_lt (by omega)]
  exact lt24

private theorem check_ready_mem (state : MachineState) :
    (checkReadyState state).mem = state.mem := rfl

attribute [local irreducible] checkReadyState

/-- Normal-mode (`k ≠ 128`) checker invariant at loop entry (`pathDepth = 24`). -/
theorem check_input_invariant (input : CheckInput) :
    CheckLoopInvariant (checkReadyState (checkLengthState (submission.initialState .check input)))
      input.positions.card 24 := by
  let initial := submission.initialState .check input
  have regs := check_ready_registers initial
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have count : initial.getReg .x16 = BitVec.ofNat 64 input.positions.card := rfl
  have memEq : (checkReadyState (checkLengthState initial)).mem = initial.mem :=
    (check_ready_mem (checkLengthState initial)).trans (check_length_preserves initial).2
  refine ⟨?_, regs.2.2.2.2.2.1.trans count, regs.1, regs.2.2.2.2.2.2, by decide, by decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [check_ready_pc, count]
    have zero : BitVec.ofNat 64 input.positions.card = 0 ↔ input.positions.card = 0 := by
      constructor
      · intro equal
        have numeric := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
        exact numeric
      · rintro empty; rw [empty]; rfl
    simp only [zero]
  · rw [regs.2.1]
    intro word inside
    exact check_buffer_access 6442455072 input.positions.card word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.1]
    intro word inside i hi
    exact index_outside_scratch word i (by norm_num [LENGTH, LOG_LENGTH] at cardinal; omega) hi
  · rw [regs.2.1]
    intro word inside
    change ((checkReadyState (checkLengthState initial)).mem _).toNat < 2 ^ 24
    rw [memEq]
    exact initial_index_bound input word inside
  · rw [regs.2.2.1]
    intro word inside
    exact check_buffer_access 6576672800 (32 * input.positions.card) word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.2.1]
    intro word inside
    exact check_buffer_access 10871640096 ((2 + 4 * 24) * input.positions.card) word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.2.2.1]
    intro word inside
    exact check_buffer_access 4294971392 4 word (by decide) (by decide) inside

attribute [local irreducible] checkRootWordsState checkCapHash

/-- Cap-mode (`k = 128`) checker invariant after the top-7 root matches (`pathDepth = 17`). -/
theorem check_cap_loop_invariant (input : CheckInput) (hashed : MachineState)
    (batch : input.positions.card = BATCH) (lenOk : input.proof.length = 75776)
    (reached : hashed ∈ support (checkCapHash (submission.initialState .check input))) :
    CheckLoopInvariant (checkCapEnterLoopState (checkRootWordsState hashed 138 4)) BATCH 17 := by
  let initial := submission.initialState .check input
  have is128 : initial.getReg .x16 = 128 := by
    change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
  have isLen : initial.getReg .x17 = 75776 := by
    change BitVec.ofNat 64 input.proof.length = 75776; rw [lenOk]; rfl
  have hRegs := check_cap_hash_registers initial hashed is128 isLen reached
  let compared := checkRootWordsState hashed 138 4
  have cKeep (reg : Reg) (n6 : reg ≠ .x6) (n7 : reg ≠ .x7) : compared.getReg reg = hashed.getReg reg :=
    (check_root_words_preserves hashed 138 4 reg n6 n7).1
  have cMem : compared.mem = hashed.mem :=
    (check_root_words_preserves hashed 138 4 .x21 (by decide) (by decide)).2
  have enterKeep (reg : Reg) (n21 : reg ≠ .x21) (n26 : reg ≠ .x26) (n30 : reg ≠ .x30) :
      (checkCapEnterLoopState compared).getReg reg = compared.getReg reg := by
    simp only [checkCapEnterLoopState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n30),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n26)]
  have e24 : (checkCapEnterLoopState compared).getReg .x24 = BitVec.ofNat 64 6442455072 := by
    rw [enterKeep .x24 (by decide) (by decide) (by decide), cKeep .x24 (by decide) (by decide),
      hRegs.2.2.2.2.2.1]; rfl
  have e8 : (checkCapEnterLoopState compared).getReg .x8 = BitVec.ofNat 64 6576672800 := by
    rw [enterKeep .x8 (by decide) (by decide) (by decide), cKeep .x8 (by decide) (by decide),
      hRegs.2.2.2.2.1]; rfl
  have e25 : (checkCapEnterLoopState compared).getReg .x25 = BitVec.ofNat 64 10871640096 := by
    rw [enterKeep .x25 (by decide) (by decide) (by decide), cKeep .x25 (by decide) (by decide),
      hRegs.2.2.2.2.2.2.1]; rfl
  have e26 : (checkCapEnterLoopState compared).getReg .x26 = BitVec.ofNat 64 (10871640096 + 71680) := by
    simp only [checkCapEnterLoopState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x21 ≠ .x26),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x26),
      MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
      cKeep .x19 (by decide) (by decide), hRegs.2.2.2.1]
    rfl
  have e27 : (checkCapEnterLoopState compared).getReg .x27 = BitVec.ofNat 64 BATCH := by
    rw [enterKeep .x27 (by decide) (by decide) (by decide), cKeep .x27 (by decide) (by decide),
      hRegs.2.2.2.2.2.2.2]; rfl
  refine ⟨rfl, e27, rfl, rfl, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e24]; intro word hw; exact check_buffer_access _ BATCH word (by decide) (by decide) hw
  · rw [e24]; intro word hw i hi; exact index_outside_scratch word i (by change word < 128 at hw; omega) hi
  · rw [e24]
    intro word hw
    change ((checkCapEnterLoopState compared).mem _).toNat < 2 ^ 24
    have memEq : (checkCapEnterLoopState compared).mem = hashed.mem := cMem
    rw [memEq]
    change (hashed.getMem (BitVec.ofNat 64 6442455072 + BitVec.ofNat 64 (8 * word))).toNat < 2 ^ 24
    rw [check_cap_hash_support_outside initial hashed isLen reached _ (Or.inr (by
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by change word < 128 at hw; omega)]
      omega))]
    exact initial_index_bound input word (by rw [batch]; exact hw)
  · rw [e8]; intro word hw; exact check_buffer_access _ (32 * BATCH) word (by decide) (by decide) hw
  · rw [e25]; intro word hw
    exact check_buffer_access _ ((2 + 4 * 17) * BATCH) word (by decide) (by decide) hw
  · rw [e26]; intro word hw
    exact check_buffer_access _ (4 * 2 ^ (24 - 17)) word (by decide) (by decide) hw

private theorem run_check_valid (candidate : Submission) (input : CheckInput)
    (valid : input.proof.length ≤ candidate.sizes.proof) :
    candidate.run .check input = execute (candidate.image .check) (candidate.steps .check)
      (candidate.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]
  rfl

attribute [local irreducible] execute pathInstructions checkPositionNextState
  checkPositionHash

set_option maxHeartbeats 600000 in
/-- Every actual checker run terminates, including malformed lengths, cap-mode proofs,
and incorrect proof contents. Uses at most `1612 * k + 25` cycles and `32 * k` public queries. -/
theorem check_input_resources (input : CheckInput) (result : Execution)
    (reachable : result ∈ support (submission.run .check input)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ 1612 * input.positions.card + 25 ∧
      result.oracleCalls ≤ 32 * input.positions.card := by
  have cardinal : input.positions.card ≤ 2 ^ 24 := by
    have card : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact card
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · by_cases batch : input.positions.card = BATCH
    · by_cases rightLen : input.proof.length = 75776
      · let initial := submission.initialState .check input
        have is128 : initial.getReg .x16 = 128 := by
          change BitVec.ofNat 64 input.positions.card = 128; rw [batch]; rfl
        have isLen : initial.getReg .x17 = 75776 := by
          change BitVec.ofNat 64 input.proof.length = 75776; rw [rightLen]; rfl
        let extra := submission.steps .check - (4118 + 15 + 4 + (1412 * BATCH + 3))
        have hsteps : submission.steps .check = 214748365824 := rfl
        have budget : submission.steps .check =
            4118 + (15 + (4 + (1412 * BATCH + 3 + extra))) := by
          dsimp [extra]; rw [hsteps]; decide
        rw [run_check_valid submission input valid, budget,
          check_cap_hash initial rfl is128 isLen rfl] at reachable
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
        obtain ⟨hashed, hashedReached, cont, contReached, rfl⟩ := reachable
        have hRegs := check_cap_hash_registers initial hashed is128 isLen hashedReached
        have scratchValid : ∀ word < 4,
            accessValid (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true := by
          rw [hRegs.2.1]; intro word hw; interval_cases word <;> decide
        have targetValid : ∀ word < 4,
            accessValid (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true := by
          rw [hRegs.2.2.1]; intro word hw
          exact check_buffer_access 4294971392 4 word (by decide) (by decide) hw
        by_cases agrees : ∀ word < 4,
            hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
              hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word))
        · have compPC : (checkRootWordsState hashed 138 4).pc = 4696 :=
            check_root_words_pc hashed 138 (Or.inr rfl) hRegs.1 4 (by decide) agrees
          rw [show 15 + (4 + (1412 * BATCH + 3 + extra)) =
              12 + (4 + (1412 * BATCH + 3 + (extra + 3))) by omega,
            check_root_matches hashed 138 (Or.inr rfl) hRegs.1 scratchValid targetValid agrees,
            check_cap_enter_loop _ compPC] at contReached
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at contReached
          obtain ⟨afterEnter, ⟨loopRes, loopReached, rfl⟩, rfl⟩ := contReached
          have inv := check_cap_loop_invariant input hashed batch rightLen hashedReached
          have res := check_loop_terminates _ BATCH 17 (by decide) inv (extra + 3) false loopRes loopReached
          simp only [Execution.charge, batch, BATCH] at res ⊢
          exact ⟨res.1, by omega, by omega⟩
        · obtain ⟨failed, run, exit, cyc, calls⟩ :=
            check_root_rejects hashed 138 (Or.inr rfl) hRegs.1 scratchValid targetValid agrees
              (4 + (1412 * BATCH + 3 + extra)) false
          rw [run] at contReached
          simp only [support_pure, Set.mem_singleton_iff] at contReached
          subst cont
          simp only [Execution.charge, exit, batch, BATCH]
          exact ⟨by decide, by omega, by omega⟩
      · rw [check_input_cap_wrong_length input valid batch rightLen] at reachable
        simp only [support_pure, Set.mem_singleton_iff] at reachable
        subst result
        exact ⟨by change Exit.failure ≠ Exit.unfinished; decide, by dsimp; omega, by dsimp; omega⟩
    · by_cases rightLength : input.proof.length = 784 * input.positions.card
      · let initial := submission.initialState .check input
        have not128 : initial.getReg .x16 ≠ 128 := by
          intro h; have n := congrArg BitVec.toNat h
          change input.positions.card % 2^64 = 128 at n
          rw [Nat.mod_eq_of_lt (by omega)] at n; exact batch n
        have invariant := check_input_invariant input
        have lengthPC : (checkLengthState initial).pc = 4144 :=
          if_pos ((check_input_length input valid).mpr rightLength)
        let extra := submission.steps .check - (1412 * input.positions.card + 18)
        have budget : submission.steps .check = 12 + (3 + (1412 * input.positions.card + 3 + extra)) := by
          change 214748365824 = 12 + (3 + (1412 * input.positions.card + 3 +
            (214748365824 - (1412 * input.positions.card + 18))))
          omega
        rw [run_check_valid submission input valid, budget,
          check_length_gate initial rfl not128, check_ready _ lengthPC] at reachable
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
        obtain ⟨afterReady, ⟨loopResult, loopReached, rfl⟩, rfl⟩ := reachable
        have resources := check_loop_terminates _ input.positions.card 24 cardinal invariant extra false
          loopResult loopReached
        simp only [Execution.charge]
        exact ⟨resources.1, by omega, by omega⟩
      · rw [check_input_wrong_length input valid batch rightLength] at reachable
        simp only [support_pure, Set.mem_singleton_iff] at reachable
        subst result
        exact ⟨by change Exit.failure ≠ Exit.unfinished; decide, by dsimp; omega, by dsimp; omega⟩
  · rw [check_oversized input (by omega)] at reachable
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst result
    exact ⟨by change Exit.failure ≠ Exit.unfinished; decide, by dsimp; omega, by dsimp; omega⟩

/-- In the scored batch the checker needs at most 4096 public calls and 206361 cycles. -/
theorem check_batch_resources (input : CheckInput) (batch : input.positions.card = BATCH)
    (result : Execution) (reachable : result ∈ support (submission.run .check input)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ 206361 ∧ result.oracleCalls ≤ 4096 := by
  simpa [batch, BATCH] using check_input_resources input result reachable

private theorem writer_run_support (impl : QueryImpl World (AddWriterT Nat ProbComp))
    {α : Type} (computation : OracleComp World α) (result : α × Multiplicative Nat)
    (reachable : result ∈ support (simulateQ impl computation).run) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
    simp only [simulateQ_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at reachable
    subst result
    simp
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind,
      support_bind, support_map, Set.mem_iUnion, exists_prop, Set.mem_image] at reachable
    obtain ⟨⟨answer, cost⟩, _, ⟨value, extra⟩, reached, rfl⟩ := reachable
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨answer, mem_support_query query answer, ih answer (value, extra) reached⟩

/-- Checker termination in the exact probabilistic form required by the submission certificate. -/
theorem check_termination (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$> (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  exact (check_input_resources input result.1
    (writer_run_support (oracle.world.withAddCost Oracle.callCost)
      (submission.run .check input) result reachable)).1

theorem check_counted (oracle : Oracle) (input : CheckInput) (result : Execution × Nat)
    (reachable : result ∈ support (oracle.run (submission.run .check input))) :
    result.1.oracleCalls = result.2 := by
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · rw [run_check_valid submission input valid] at reachable
    exact execute_counted oracle _ _ _ result reachable
  · rw [check_oversized input (by omega), oracle_run_pure] at reachable
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst result
    rfl

/-- Simultaneous termination and resource bounds through the security game's actual oracle runner. -/
theorem check_oracle_resources (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished ∧
      result.1.cycles ≤ 1612 * input.positions.card + 25 ∧ result.2 ≤ 32 * input.positions.card) <$> (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  have resources := check_input_resources input result.1
    (writer_run_support (oracle.world.withAddCost Oracle.callCost)
      (submission.run .check input) result reachable)
  exact ⟨resources.1, resources.2.1, by rw [← check_counted oracle input result reachable]; exact resources.2.2⟩

end CommitGolfCandidate
