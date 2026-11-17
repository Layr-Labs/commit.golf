import CommitGolfCandidate.CapDfsRun

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def capOpenDfsNext (marked : Nat → Bool) :
    CapDfsControl → MachineState → MachineState
  | .visit node, state =>
      if marked node then capMarkedVisitState false state node else capUnknownOpenState state
  | .advance node, state =>
      if node = 1 then capAdvanceRootState false state
      else if node % 2 = 0 then capAdvanceSiblingState false state
      else capAdvanceOpenAscentState state
  | .done, state => state

def capOpenDfsFinal (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → MachineState
  | 0, _, state => state
  | count+1, control, state =>
      capOpenDfsFinal marked count (capControlStep marked control)
        (capOpenDfsNext marked control state)

theorem cap_open_dfs_step_pure (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) :
    capDfsStep false marked control state = pure (capOpenDfsNext marked control state) := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, capOpenDfsNext, if_pos present]
      · simp only [capDfsStep, capOpenDfsNext, if_neg present,
          Bool.false_eq_true, ite_false]
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, capOpenDfsNext, if_pos root]
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, capOpenDfsNext, if_neg root, if_pos even]
        · simp only [capDfsStep, capOpenDfsNext, if_neg root, if_neg even,
            Bool.false_eq_true, ite_false]
  | done => rfl

theorem cap_open_dfs_run_pure (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) (state : MachineState) :
    capDfsRun false marked count control state =
      pure (capOpenDfsFinal marked count control state) := by
  induction count generalizing control state with
  | zero => rfl
  | succ count ih =>
      rw [capDfsRun, cap_open_dfs_step_pure, pure_bind, ih]
      rfl

end CommitGolfCandidate
