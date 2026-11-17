import CommitGolfCandidate.CapCheckCompleteBudget

/-! Query budget of the actual experimental checker on every ABI input.
Oversized proofs reject before loading, short lower prefixes reject before
proof access, and empty requests make no queries. Nonempty admitted requests
use the supported record/cap bound, including malformed cap tails. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute

theorem cap_check_program_fuel (input : CheckInput) :
    29+671*input.positions.card+19945 ≤ capProgram.steps .check := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  norm_num [capProgram, capExperimental, candidate, LENGTH, LOG_LENGTH] at cardinal ⊢
  omega

theorem cap_check_program_queries (input : CheckInput) :
    (capProgram.run .check input).IsTotalQueryBound (26*input.positions.card) := by
  by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
  · change (if decide (input.proof.length ≤ capProgram.sizes.proof) then
        execute (capProgram.image .check) (capProgram.steps .check)
          (capProgram.initialState .check input) false
      else pure ⟨.failure, initialMachine, 0, 0⟩).IsTotalQueryBound _
    simp only [admitted, decide_true, ite_true]
    have sufficient := cap_check_program_fuel input
    by_cases enough : 544*input.positions.card ≤ input.proof.length
    · by_cases empty : input.positions.card = 0
      · have execution := cap_check_input_empty input admitted empty
          (capProgram.steps .check-16) false
        rw [show 16+(capProgram.steps .check-16)=capProgram.steps .check by omega]
          at execution
        rw [execution]
        trivial
      · have execution := cap_check_input_nonempty input admitted enough (by omega)
          (capProgram.steps .check-29) false
        rw [show 29+(capProgram.steps .check-29)=capProgram.steps .check by omega]
          at execution
        rw [execution]
        simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
          cap_check_nonempty_continue_budget input admitted enough (by omega)
            (capProgram.steps .check-29) (by omega) false
    · have execution := cap_check_short_reject input admitted (by omega)
        (capProgram.steps .check-14) false
      rw [show 14+(capProgram.steps .check-14)=capProgram.steps .check by omega]
        at execution
      rw [execution]
      trivial
  · simp only [Submission.run, admitted, decide_false, ite_false]
    trivial

end CommitGolfCandidate
