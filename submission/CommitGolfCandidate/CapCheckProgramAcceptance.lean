import CommitGolfCandidate.CapCheckRecordsAcceptance
import CommitGolfCandidate.CapCheckOracleResources

/-! Acceptance of the actual checker scheme for every ABI input. Oversized
and short proofs reject before a proof load. Empty positions accept only the
empty proof. Nonempty inputs run the paid forward lower records and strict cap
decoder, retaining the original commitment, values and all trailing bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation execute

def CapCheckProgramAccepts (oracle : Oracle) (input : CheckInput) : Prop :=
  input.proof.length ≤ capProgram.sizes.proof ∧
  if input.positions.card=0 then input.proof=[] else
    576*input.positions.card ≤ input.proof.length ∧
    ∃ roots, capLowerBatchRoots oracle.compression (capCheckLoadedRecords input)
      (fun _ => none)=some roots ∧ CapCheckLoadedAcceptance oracle input roots

theorem cap_check_program_acceptance (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (capProgram.run .check input)).1.exit=.success ↔
      CapCheckProgramAccepts oracle input := by
  have sufficient := cap_check_program_fuel input
  by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
  · change (checkEvaluation oracle
      (if decide (input.proof.length ≤ capProgram.sizes.proof) then
        execute (capProgram.image .check) (capProgram.steps .check)
          (capProgram.initialState .check input) false
      else pure ⟨.failure,initialMachine,0,0⟩)).1.exit=.success ↔ _
    simp only [admitted,decide_true,ite_true,CapCheckProgramAccepts,true_and]
    by_cases enough : 576*input.positions.card ≤ input.proof.length
    · by_cases empty : input.positions.card=0
      · have execution := cap_check_input_empty input admitted empty
          (capProgram.steps .check-16) false
        rw [show 16+(capProgram.steps .check-16)=capProgram.steps .check by omega]
          at execution
        rw [execution]
        simp only [check_evaluation_pure,empty,ite_true]
        by_cases zero : input.proof.length=0
        · simp only [zero,ite_true,true_iff]
          exact List.length_eq_zero_iff.mp zero
        · simp only [zero,ite_false,reduceCtorEq,false_iff]
          intro nil
          rw [nil] at zero
          exact zero rfl
      · have execution := cap_check_input_nonempty input admitted enough (by omega)
          (capProgram.steps .check-29) false
        rw [show 29+(capProgram.steps .check-29)=capProgram.steps .check by omega]
          at execution
        rw [execution,cap_check_evaluation_bind_value,check_evaluation_pure]
        let state := capCheckRecordEntry
          (capCheckLengthState (capProgram.initialState .check input))
        have ready := cap_check_records_ready_initial input (by omega)
        rw [cap_check_records_execute input admitted enough 0 input.positions.card
          state ready (capProgram.steps .check-29) (by omega) false]
        change (checkEvaluation oracle (capCheckRecordsContinue input.positions.card
          state (capProgram.steps .check-29) false)).1.exit=.success ↔ _
        rw [cap_check_records_continue_acceptance oracle input admitted enough 0
          input.positions.card state ready (fun _ => none)
          (cap_check_collected_initial input) (fun zero => False.elim (empty zero))
          (capProgram.steps .check-29) (by omega) false]
        simp only [List.drop_zero,empty,ite_false,enough,true_and]
    · have execution := cap_check_short_reject input admitted (by omega)
        (capProgram.steps .check-14) false
      rw [show 14+(capProgram.steps .check-14)=capProgram.steps .check by omega]
        at execution
      rw [execution]
      have nonempty : input.positions.card≠0 := by
        intro zero
        rw [zero] at enough
        exact enough (Nat.zero_le _)
      simp only [check_evaluation_pure,reduceCtorEq,nonempty,ite_false,enough,
        false_and]
  · simp only [Submission.run,admitted,decide_false,ite_false,check_evaluation_pure,
      reduceCtorEq,CapCheckProgramAccepts,false_and]

theorem cap_check_scheme_acceptance (oracle : Oracle) (input : CheckInput) :
    (oracle.eval (capProgram.scheme.check input.commitment input.positions
      input.values input.proof)).1=true ↔ CapCheckProgramAccepts oracle input := by
  rw [scheme_check_evaluation]
  change decide ((checkEvaluation oracle (capProgram.run .check input)).1.exit=.success)=
    true ↔ _
  rw [decide_eq_true_eq]
  exact cap_check_program_acceptance oracle input

end CommitGolfCandidate
