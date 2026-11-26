import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.InputOrder

/-! Discharge the checker's invariants using the trusted input ABI, and derive
termination, resource bounds, and exact acceptance for every fixed oracle. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

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

/-- Every actual checker input establishes the post-gate memory-safety and index-range
conditions. The proof's content, commitment, and opened values remain arbitrary. -/
theorem check_input_invariant (input : CheckInput) :
    CheckReadyInvariant (checkReadyState (checkLengthState (submission.initialState .check input)))
      input.positions.card := by
  let initial := submission.initialState .check input
  have regs := check_ready_registers initial
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal ⊢; omega
  have count : initial.getReg .x16 = BitVec.ofNat 64 input.positions.card := rfl
  have indexPointer : (checkReadyState (checkLengthState initial)).getReg .x24 =
      BitVec.ofNat 64 6442455072 := regs.2.1
  have memory : (checkReadyState (checkLengthState initial)).mem = initial.mem := check_ready_memory initial
  refine ⟨?_, regs.2.2.2.2.2.trans count, regs.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [check_ready_pc, count]
    have zero : BitVec.ofNat 64 input.positions.card = 0 ↔ input.positions.card = 0 := by
      constructor
      · intro equal
        have numeric := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
        exact numeric
      · rintro empty; rw [empty]; rfl
    simp only [zero]
  · rw [indexPointer]
    intro word inside
    exact check_buffer_access _ input.positions.card word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [indexPointer]
    intro word inside
    have address : BitVec.ofNat 64 6442455072 + BitVec.ofNat 64 (8 * word) =
        BitVec.ofNat 64 (submission.layout.indices + 8 * word) := by
      rw [← BitVec.ofNat_add]; rfl
    have same : (checkReadyState (checkLengthState initial)).getMem = initial.getMem :=
      congrArg (fun mem address => mem address) memory
    rw [address, same, check_input_position input word inside]
    have bound := opening_index_bound input.positions word
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num [LENGTH, LOG_LENGTH] at bound ⊢; omega)]
    simpa [LENGTH, LOG_LENGTH] using bound
  · rw [indexPointer]
    intro word inside i hi equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at natural
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    rw [Nat.mod_eq_of_lt (by omega : 8 * word < 2^64),
      Nat.mod_eq_of_lt (by omega : 6442455072 + 8 * word < 2^64),
      Nat.mod_eq_of_lt (by omega : 256 + 8 * i < 2^64)] at natural
    omega
  · rw [regs.2.2.1]
    change ∀ word < 32 * input.positions.card,
      accessValid (BitVec.ofNat 64 6576672800 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ (32 * input.positions.card) word (by
      norm_num [LENGTH, LOG_LENGTH, MEMORY_BYTES] at cardinal ⊢; omega) (by decide) inside
  · rw [regs.2.2.2.1]
    change ∀ word < 512 + 71 * input.positions.card,
      accessValid (BitVec.ofNat 64 10871640096 + BitVec.ofNat 64 (8 * word)) 8 = true
    intro word inside
    exact check_buffer_access _ (512 + 71 * input.positions.card) word (by
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

attribute [local irreducible] execute checkEvaluation checkReadyAccepts

set_option maxHeartbeats 1000000 in
/-- Every actual checker run, for every fixed oracle and every input, terminates with the
exact acceptance condition: the length is 4096 + 568 per position, and (for a nonempty
opening) the cap chain reproduces the commitment and every record climbs to its cap node.
At most 1100 cycles per position plus 1910, and at most 85 calls per position. -/
theorem check_input_run (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (submission.run .check input)).1.exit =
      (if input.proof.length = 4096 + 568 * input.positions.card ∧
          checkReadyAccepts oracle input.positions.card
            (checkReadyState (checkLengthState (submission.initialState .check input))) = true
        then .success else .failure) ∧
    (checkEvaluation oracle (submission.run .check input)).1.cycles ≤
      1100 * input.positions.card + 1910 ∧
    (checkEvaluation oracle (submission.run .check input)).1.oracleCalls ≤
      85 * input.positions.card := by
  have cardinal : input.positions.card ≤ 2 ^ 24 := by
    have card : input.positions.card ≤ LENGTH := by
      simpa [Index] using Finset.card_le_univ input.positions
    exact card
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · by_cases rightLength : input.proof.length = 4096 + 568 * input.positions.card
    · have lengthPC : (checkLengthState (submission.initialState .check input)).pc = 4148 := by
        rw [check_length_pc]
        exact if_pos ((check_input_length input valid).mpr rightLength)
      have budget : submission.steps .check = 13 + (4 + (1440 + 920 * input.positions.card +
          (214748372992 - (1457 + 920 * input.positions.card)))) := by
        change 214748372992 = _
        omega
      rw [run_check_valid submission input valid, budget, check_length_gate _ rfl,
        evaluation_charge, check_ready _ lengthPC, evaluation_charge]
      have run := check_ready_run oracle _ input.positions.card cardinal (check_input_invariant input)
        (214748372992 - (1457 + 920 * input.positions.card))
      simp only [Execution.charge]
      refine ⟨?_, ?_, ?_⟩
      · rw [run.1]
        simp only [rightLength, true_and]
      · have := run.2.1
        omega
      · have := run.2.2
        omega
    · rw [check_input_wrong_length input valid rightLength, check_evaluation_pure]
      simp [rightLength]
  · have oversized : submission.sizes.proof < input.proof.length := by omega
    rw [check_oversized input oversized, check_evaluation_pure]
    have notLength : input.proof.length ≠ 4096 + 568 * input.positions.card := by
      rw [submission_proof_capacity] at oversized
      norm_num [LENGTH, LOG_LENGTH] at oversized cardinal
      omega
    simp [notLength]

theorem check_input_exit (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (submission.run .check input)).1.exit ≠ .unfinished := by
  rw [(check_input_run oracle input).1]
  split <;> decide

/-- In the scored batch the checker needs at most 10880 public calls and 142710 cycles.
Checking cycles are not part of the prover's score. -/
theorem check_batch_resources (oracle : Oracle) (input : CheckInput)
    (batch : input.positions.card = BATCH) :
    (checkEvaluation oracle (submission.run .check input)).1.exit ≠ .unfinished ∧
    (checkEvaluation oracle (submission.run .check input)).1.cycles ≤ 142710 ∧
    (checkEvaluation oracle (submission.run .check input)).1.oracleCalls ≤ 10880 := by
  have run := check_input_run oracle input
  rw [batch] at run
  exact ⟨check_input_exit oracle input, by simpa [BATCH] using run.2.1, by simpa [BATCH] using run.2.2⟩

/-- Checker termination in the exact probabilistic form required by the submission
certificate, for every fixed oracle and every input (honest or adversarial). -/
theorem check_termination (oracle : Oracle) (input : CheckInput) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$>
      (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  rw [check_run_evaluation] at reachable
  simp only [support_pure, Set.mem_singleton_iff] at reachable
  subst result
  exact check_input_exit oracle input

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
      result.1.cycles ≤ 1100 * input.positions.card + 1910 ∧
      result.2 ≤ 85 * input.positions.card) <$> (oracle.run (submission.run .check input)))) = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reachable
  have counted := check_counted oracle input result reachable
  rw [check_run_evaluation] at reachable
  simp only [support_pure, Set.mem_singleton_iff] at reachable
  subst result
  have run := check_input_run oracle input
  exact ⟨check_input_exit oracle input, run.2.1, by rw [← counted]; exact run.2.2⟩

/-- The deterministic check count used by the security games obeys the interpreter
proof for every proof, commitment, value vector, and index set: 85 calls per position. -/
theorem scheme_check_budget (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      85 * input.positions.card := by
  rw [scheme_check_evaluation]
  have reached : checkEvaluation oracle (submission.run .check input) ∈
      support (oracle.run (submission.run .check input)) := by
    rw [check_run_evaluation]
    simp
  have counted := check_counted oracle input _ reached
  rw [← counted]
  exact (check_input_run oracle input).2.2

/-- Exact acceptance through the trusted ABI. -/
theorem check_input_acceptance (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (submission.run .check input)).1.exit = .success ↔
      input.proof.length = 4096 + 568 * input.positions.card ∧
        checkReadyAccepts oracle input.positions.card
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  rw [(check_input_run oracle input).1]
  split
  · simp_all
  · simp_all

/-- The security-game scheme uses this same acceptance condition, not an abstract
checker substituted for the submitted program. -/
theorem scheme_check_acceptance (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true ↔
      input.proof.length = 4096 + 568 * input.positions.card ∧
        checkReadyAccepts oracle input.positions.card
          (checkReadyState (checkLengthState (submission.initialState .check input))) = true := by
  rw [scheme_check_evaluation]
  simp only [beq_iff_eq]
  exact check_input_acceptance oracle input

end CommitGolfCandidate
