import CommitGolfCandidate.CapCheckDfsEvaluation
import CommitGolfCandidate.CapCheckDfsFinish

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation capCheckDfsNext capCheckDfsValue

theorem cap_check_finish_exit_value (oracle : Oracle) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    (checkEvaluation oracle (capCheckDfsFinish marked count control state)).1.exit=
      if (capCheckDfsValue oracle marked count control state).2 then
        (capCheckFinalResult
          (capCheckDfsValue oracle marked count control state).1).exit
      else .failure := by
  induction count generalizing control state with
  | zero =>
    simp only [capCheckDfsFinish,capCheckDfsValue,check_evaluation_pure,↓reduceIte]
  | succ count ih =>
    rw [capCheckDfsFinish,capCheckDfsValue]
    cases short : capCheckDfsShort marked control state
    · simp only [short,Bool.false_eq_true,↓reduceIte]
      rw [cap_check_evaluation_bind_value,cap_check_dfs_step_evaluation,
        cap_check_evaluation_bind_value,check_evaluation_pure]
      change (checkEvaluation oracle
        (capCheckDfsFinish marked count (capControlStep marked control)
          (capCheckDfsNext oracle marked control state))).1.exit=_
      exact ih (capControlStep marked control)
        (capCheckDfsNext oracle marked control state)
    · simp only [short,Bool.false_eq_true,↓reduceIte,check_evaluation_pure]

end CommitGolfCandidate
