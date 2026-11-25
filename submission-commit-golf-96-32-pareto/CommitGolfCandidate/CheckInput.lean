import CommitGolfCandidate.CheckLoop
import CommitGolfCandidate.Counting

/-! Discharge the checker loop's invariants using the trusted input ABI. -/
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

/-- Every actual checker input establishes the outer loop's memory-safety conditions.
The proof's content, commitment, and opened values remain arbitrary. -/
theorem check_input_invariant (input : CheckInput) :
    CheckLoopInvariant (checkReadyState (checkLengthState (submission.initialState .check input)))
      input.positions.card := by
  let initial := submission.initialState .check input
  have regs := check_ready_registers initial
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have count : initial.getReg .x16 = BitVec.ofNat 64 input.positions.card := rfl
  refine ⟨?_, regs.2.2.2.2.2.trans count, regs.1, ?_, ?_, ?_, ?_⟩
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
    change ∀ word < input.positions.card,
      accessValid (BitVec.ofNat 64 5905584160 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ input.positions.card word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.1]
    change ∀ word < 32 * input.positions.card,
      accessValid (BitVec.ofNat 64 6039801888 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ (32 * input.positions.card) word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.2.1]
    change ∀ word < 100 * input.positions.card,
      accessValid (BitVec.ofNat 64 10334769184 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ (100 * input.positions.card) word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.2.2.1]
    change ∀ word < 4,
      accessValid (BitVec.ofNat 64 4294971392 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ 4 word (by decide) (by decide) inside

private theorem run_check_valid (candidate : Submission) (input : CheckInput)
    (valid : input.proof.length ≤ candidate.sizes.proof) :
    candidate.run .check input = execute (candidate.image .check) (candidate.steps .check)
      (candidate.initialState .check input) false := by
  simp only [Submission.run, valid, decide_true, if_true]
  rfl

attribute [local irreducible] execute pathInstructions checkRootWordsState checkPositionNextState
  checkPositionHash

/-- Every actual checker run terminates, including malformed lengths and incorrect
proof contents. At most 32 calls and 1612 cycles per position, plus 20 setup/exit
cycles, are needed. No correctness assumption about the proof is used. -/
theorem check_input_resources (input : CheckInput) (result : Execution)
    (reachable : result ∈ support (submission.run .check input)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ 1612 * input.positions.card + 20 ∧
      result.oracleCalls ≤ 32 * input.positions.card := by
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · by_cases rightLength : input.proof.length = 800 * input.positions.card
    · let initial := submission.initialState .check input
      have invariant := check_input_invariant input
      have cardinal : input.positions.card ≤ 2 ^ 24 := by
        have card : input.positions.card ≤ LENGTH := by
          simpa [Index] using Finset.card_le_univ input.positions
        exact card
      have lengthPC : (checkLengthState initial).pc = 4136 :=
        if_pos ((check_input_length input valid).mpr rightLength)
      let extra := submission.steps .check - (1412 * input.positions.card + 17)
      have budget : submission.steps .check = 10 + (4 + (1412 * input.positions.card + 3 + extra)) := by
        change 214748365824 = 10 + (4 + (1412 * input.positions.card + 3 +
          (214748365824 - (1412 * input.positions.card + 17))))
        omega
      rw [run_check_valid submission input valid] at reachable
      rw [budget, check_length_gate initial rfl, check_ready _ lengthPC] at reachable
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
      obtain ⟨afterReady, ⟨loopResult, loopReached, rfl⟩, rfl⟩ := reachable
      have resources := check_loop_terminates _ input.positions.card cardinal invariant extra false
        loopResult loopReached
      simp only [Execution.charge]
      exact ⟨resources.1, by omega, by omega⟩
    · rw [check_input_wrong_length input valid rightLength] at reachable
      simp only [support_pure, Set.mem_singleton_iff] at reachable
      subst result
      exact ⟨by change Exit.failure ≠ Exit.unfinished; decide, by dsimp; omega, by dsimp; omega⟩
  · rw [check_oversized input (by omega)] at reachable
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst result
    exact ⟨by change Exit.failure ≠ Exit.unfinished; decide, by dsimp; omega, by dsimp; omega⟩

/-- In the scored batch the checker needs at most 4096 public calls and 206356
cycles. Checking cycles are not part of the prover's score; the call bound is a
separate security/correctness requirement. -/
theorem check_batch_resources (input : CheckInput) (batch : input.positions.card = BATCH)
    (result : Execution) (reachable : result ∈ support (submission.run .check input)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ 206356 ∧ result.oracleCalls ≤ 4096 := by
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

/-- Checker termination in the exact probabilistic form required by the submission
certificate, for every fixed oracle and every input (honest or adversarial). -/
theorem check_termination (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$> (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  exact (check_input_resources input result.1
    (writer_run_support (oracle.world.withAddCost Oracle.callCost)
      (submission.run .check input) result reachable)).1

/-- The call count used by the security games agrees with the checker's machine
counter. Oversized inputs are rejected before either counter is incremented. -/
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

/-- Simultaneous termination and resource bounds through the security game's actual
oracle runner. The query bound concerns the runner's counter, not a claimed counter. -/
theorem check_oracle_resources (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished ∧
      result.1.cycles ≤ 1612 * input.positions.card + 20 ∧ result.2 ≤ 32 * input.positions.card) <$> (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  have resources := check_input_resources input result.1
    (writer_run_support (oracle.world.withAddCost Oracle.callCost)
      (submission.run .check input) result reachable)
  exact ⟨resources.1, resources.2.1, by rw [← check_counted oracle input result reachable]; exact resources.2.2⟩

end CommitGolfCandidate
