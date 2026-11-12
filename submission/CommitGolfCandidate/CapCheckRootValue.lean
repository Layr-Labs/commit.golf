import CommitGolfCandidate.CapCheckCodecAlgebra
import CommitGolfCandidate.CapDfsBoundaryOrder

/-! The conservative 1022-step traversal is the root subtree, its actual root
completion edge and zero-cost done padding. Rejection in the subtree remains
rejection and cannot resume at the root edge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckDfsNext capCheckDfsValue capCheckSubtreeValue

theorem cap_check_done_value (oracle : Oracle) (marked : Nat → Bool)
    (count : Nat) (state : MachineState) :
    capCheckDfsValue oracle marked count .done state=(state,true) := by
  induction count with
  | zero => rw [capCheckDfsValue]
  | succ count ih =>
    rw [capCheckDfsValue]
    simpa only [capCheckDfsShort,Bool.false_eq_true,↓reduceIte,
      capControlStep,capCheckDfsNext] using ih

theorem cap_check_root_value (oracle : Oracle) (marked : Nat → Bool)
    (state : MachineState) :
    capCheckDfsValue oracle marked 1022 (.visit 1) state=
      capCheckValueThen (capCheckSubtreeValue oracle marked 8 1 state)
        (fun last => (capCheckDfsNext oracle marked (.advance 1) last,true)) := by
  have bound := cap_subtree_steps_bound marked 8 1
  have bounded : capSubtreeSteps marked 8 1≤1021 := by
    norm_num at bound
    omega
  have count : 1022=capSubtreeSteps marked 8 1+(1+(1021-capSubtreeSteps marked 8 1)) := by
    omega
  rw [count,cap_check_dfs_value_add,
    cap_subtree_run_end marked 8 1 (by decide) (by decide),
    cap_check_subtree_value oracle marked 8 1 state (by decide) (by decide)]
  apply congrArg (capCheckValueThen (capCheckSubtreeValue oracle marked 8 1 state))
  funext last
  rw [Nat.add_comm 1,cap_check_dfs_value_head]
  have one := cap_check_one_value oracle marked (.advance 1) last rfl
  rw [one]
  change capCheckDfsValue oracle marked (1021-capSubtreeSteps marked 8 1)
    .done (capCheckDfsNext oracle marked (.advance 1) last)=_
  exact cap_check_done_value oracle marked _ _

end CommitGolfCandidate
