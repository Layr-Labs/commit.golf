import CommitGolfCandidate.CapCheckRecordsExecution
import CommitGolfCandidate.CapCheckEvaluationValue

/-! Value projection of the actual record continuation. The fuel reserve and
charges remain in the execution; this lemma only exposes its exit decision
under a fixed oracle. A duplicate rejection never executes the later records. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation capCheckLowerRecord

theorem cap_check_continue_exit_head (oracle : Oracle) (count : Nat)
    (state : MachineState) (fuel : Nat) (allowCoins : Bool) :
    (checkEvaluation oracle
      (capCheckRecordsContinue (count+1) state fuel allowCoins)).1.exit =
      if (capCheckGroupResult (checkEvaluation oracle (capCheckLowerRecord state)).1).2 then
        (checkEvaluation oracle (capCheckRecordsContinue count
          (capCheckRecordResult (checkEvaluation oracle (capCheckLowerRecord state)).1).1
          (fuel-capCheckLowerRecordSteps state-
            capCheckGroupSteps (checkEvaluation oracle (capCheckLowerRecord state)).1-3)
          allowCoins)).1.exit
      else .failure := by
  rw [capCheckRecordsContinue,cap_check_evaluation_bind_value]
  cases passed : (capCheckGroupResult
      (checkEvaluation oracle (capCheckLowerRecord state)).1).2
  · simp only [passed,Bool.false_eq_true,↓reduceIte,check_evaluation_pure]
  · simp only [passed,↓reduceIte]
    rw [cap_check_evaluation_bind_value,check_evaluation_pure]
    rfl

end CommitGolfCandidate
