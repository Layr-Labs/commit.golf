import CommitGolfCandidate.CapCheckStart

/-! ABI specialization of the two initial checker decisions. Proof contents
and opened values are arbitrary. The minimum length test and empty request
test use admitted natural lengths, so neither can silently wrap a word. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckLengthState capCheckRecordEntry

theorem cap_check_input_count (input : CheckInput) :
    (capCheckLengthState (capProgram.initialState .check input)).getReg .x27 =
      BitVec.ofNat 64 input.positions.card :=
  cap_check_length_count _

theorem cap_check_input_length_zero (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof) :
    (capCheckLengthState (capProgram.initialState .check input)).getReg .x17 = 0 ↔
      input.proof.length = 0 := by
  rw [cap_check_length_proof_length]
  change BitVec.ofNat 64 input.proof.length = 0 ↔ input.proof.length = 0
  have small : input.proof.length < 2^64 := by
    have bounded := (cap_check_loader_bounds input admitted).2.2
    omega
  constructor
  · intro zero
    have numeric := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    change input.proof.length = 0 at numeric
    exact numeric
  · intro zero
    rw [zero]
    rfl

private theorem empty_result (state : MachineState) (length : Nat)
    (zero : state.getReg .x17 = 0 ↔ length = 0) :
    (pure (⟨if state.getReg .x17 = 0 then .success else .failure,
      capCheckExitState (capCheckEmptyState state)
        (decide (state.getReg .x17 = 0)), 19, 0⟩ : Execution) :
      OracleComp World Execution) =
    pure ⟨if length = 0 then .success else .failure,
      capCheckExitState (capCheckEmptyState state) (decide (length = 0)), 19, 0⟩ := by
  by_cases empty : length = 0
  · have word := zero.mpr empty
    simp only [word, empty, if_true, decide_true]
  · have word : ¬ state.getReg .x17 = 0 := fun h => empty (zero.mp h)
    simp only [word, empty, if_false, decide_false]

/-- Empty requests run sixteen actual instructions and accept exactly []. -/
theorem cap_check_input_empty (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (empty : input.positions.card = 0) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (16 + fuel)
      (capProgram.initialState .check input) allowCoins =
      pure ⟨if input.proof.length = 0 then .success else .failure,
        capCheckExitState
          (capCheckEmptyState (capCheckLengthState (capProgram.initialState .check input)))
          (decide (input.proof.length = 0)), 19, 0⟩ := by
  let initial := capProgram.initialState .check input
  have pc : (capCheckLengthState initial).pc = 4140 := by
    rw [cap_check_length_decision input admitted, empty]
    simp
  have count : (capCheckLengthState initial).getReg .x27 = 0 := by
    rw [cap_check_input_count, empty]
    rfl
  have gate : execute (capProgram.image .check) (11 + (5 + fuel)) initial allowCoins =
      (do let result ← execute (capProgram.image .check) (5 + fuel)
            (capCheckLengthState initial) allowCoins
          return result.charge 14 0) :=
    cap_check_length_gate initial rfl (5 + fuel) allowCoins
  have tail := cap_check_empty_tail (capCheckLengthState initial) pc count fuel allowCoins
  rw [show 16 + fuel = 11 + (5 + fuel) by omega, gate, tail]
  have zero := cap_check_input_length_zero input admitted
  change (pure (⟨if (capCheckLengthState (capProgram.initialState .check input)).getReg .x17 = 0
      then .success else .failure,
    capCheckExitState
      (capCheckEmptyState (capCheckLengthState (capProgram.initialState .check input)))
      (decide ((capCheckLengthState (capProgram.initialState .check input)).getReg .x17 = 0)),
    19, 0⟩ : Execution) : OracleComp World Execution) = _
  exact empty_result _ _ zero

/-- A sufficiently long nonempty request reaches the first actual record
after twenty-nine instructions and thirty-two cycles. -/
theorem cap_check_input_nonempty (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544 * input.positions.card ≤ input.proof.length)
    (nonempty : 0 < input.positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .check) (29 + fuel)
      (capProgram.initialState .check input) allowCoins =
      (do let result ← execute (capProgram.image .check) fuel
            (capCheckRecordEntry
              (capCheckLengthState (capProgram.initialState .check input))) allowCoins
          return result.charge 32 0) := by
  let initial := capProgram.initialState .check input
  have pc : (capCheckLengthState initial).pc = 4140 := by
    rw [cap_check_length_decision input admitted, if_neg (by omega)]
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card < 2^64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have count : (capCheckLengthState initial).getReg .x27 ≠ 0 := by
    rw [cap_check_input_count]
    intro zero
    have numeric := congrArg BitVec.toNat zero
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at numeric
    change input.positions.card = 0 at numeric
    omega
  have gate : execute (capProgram.image .check) (11 + (18 + fuel)) initial allowCoins =
      (do let result ← execute (capProgram.image .check) (18 + fuel)
            (capCheckLengthState initial) allowCoins
          return result.charge 14 0) :=
    cap_check_length_gate initial rfl (18 + fuel) allowCoins
  rw [show 29 + fuel = 11 + (18 + fuel) by omega, gate,
    cap_check_start_nonempty _ pc count fuel allowCoins]
  simp [initial, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
