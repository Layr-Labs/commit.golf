import CommitGolfCandidate.CapCheckOracleResources

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] checkEvaluation

def capCheckDfsNext (oracle : Oracle) (marked : Nat → Bool) :
    CapDfsControl → MachineState → MachineState
  | .visit node,state =>
      if marked node then capMarkedVisitState true state node else capUnknownCheckState state
  | .advance node,state =>
      if node=1 then capAdvanceRootState true state
      else if node%2=0 then capAdvanceSiblingState true state
      else capCheckAscentAnswer state (oracle.compression (capCheckAscentQuery state node))
  | .done,state => state

theorem cap_check_compression_evaluation (oracle : Oracle)
    (input : BitVec COMPRESSION_INPUT_LENGTH) :
    checkEvaluation oracle (capCheckCompression input) = (oracle.compression input,1) := by
  change checkEvaluation oracle
    (liftM (World.query (.inr (.inl input)))) = _
  rw [check_evaluation_public]
  rfl

theorem cap_check_dfs_step_evaluation (oracle : Oracle) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) :
    checkEvaluation oracle (capDfsStep true marked control state) =
      (capCheckDfsNext oracle marked control state,capDfsStepQueries true control) := by
  cases control with
  | visit node =>
    by_cases present : marked node=true
    · simp only [capDfsStep,capCheckDfsNext,if_pos present,
        capDfsStepQueries,check_evaluation_pure]
    · simp only [capDfsStep,capCheckDfsNext,if_neg present,
        ↓reduceIte,capDfsStepQueries,check_evaluation_pure]
  | advance node =>
    by_cases root : node=1
    · simp only [capDfsStep,capCheckDfsNext,capDfsStepQueries,if_pos root,
        check_evaluation_pure]
    · by_cases even : node%2=0
      · simp only [capDfsStep,capCheckDfsNext,capDfsStepQueries,if_neg root,if_pos even,
          check_evaluation_pure]
      · simp only [capDfsStep,capCheckDfsNext,capDfsStepQueries,if_neg root,if_neg even,
          ↓reduceIte,check_evaluation_bind,cap_check_compression_evaluation,
          check_evaluation_pure,Nat.add_zero]
  | done =>
    simp only [capDfsStep,capCheckDfsNext,capDfsStepQueries,check_evaluation_pure]

def capCheckDfsValue (oracle : Oracle) (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → MachineState × Bool
  | 0,_,state => (state,true)
  | count+1,control,state =>
      if capCheckDfsShort marked control state then
        (capCheckExitState (capUnknownCheckGuard state) false,false)
      else capCheckDfsValue oracle marked count (capControlStep marked control)
        (capCheckDfsNext oracle marked control state)

theorem cap_check_dfs_run_value (oracle : Oracle) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    (checkEvaluation oracle (capCheckDfsRun marked count control state)).1 =
      capCheckDfsValue oracle marked count control state := by
  induction count generalizing control state with
  | zero =>
    simp only [capCheckDfsRun,capCheckDfsValue,check_evaluation_pure]
  | succ count ih =>
    rw [capCheckDfsRun,capCheckDfsValue]
    split
    · rw [check_evaluation_pure]
    · rw [cap_check_evaluation_bind_value,cap_check_dfs_step_evaluation,ih]

end CommitGolfCandidate
