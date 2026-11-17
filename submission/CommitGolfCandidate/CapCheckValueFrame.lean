import CommitGolfCandidate.CapCheckDfsEvaluation
import CommitGolfCandidate.CapCheckDfsFrame

/-! Reachability and input frames for deterministic evaluation of the actual
checker traversal. These apply only to successful phase results; success here
does not assert the subsequent root and exact-length comparison accepts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_dfs_value_support (oracle : Oracle) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    capCheckDfsValue oracle marked count control state ∈
      support (capCheckDfsRun marked count control state) := by
  rw [←cap_check_dfs_run_value]
  exact check_evaluation_support oracle _

theorem cap_check_dfs_value_ready (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state : MachineState) (ready : CapCheckDfsReady limit marked control state)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    CapCheckDfsReady limit marked (capControlRun marked count control)
      (capCheckDfsValue oracle marked count control state).1 :=
  cap_check_dfs_run_ready limit marked count control state ready _
    (cap_check_dfs_value_support oracle marked count control state) passed

theorem cap_check_dfs_value_high (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state reference : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (frame : CapHighBytes state reference)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    CapHighBytes (capCheckDfsValue oracle marked count control state).1 reference ∧
      (capCheckDfsValue oracle marked count control state).1.getReg .x26=
        state.getReg .x26 :=
  cap_check_dfs_run_high limit marked count control state reference ready frame _
    (cap_check_dfs_value_support oracle marked count control state) passed

end CommitGolfCandidate
