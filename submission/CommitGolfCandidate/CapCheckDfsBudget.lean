import CommitGolfCandidate.CapDfsQueryCount
import CommitGolfCandidate.CapCheckDfsFinish

/-! Finer all-reply query accounting for the actual terminating cap traversal.
Early short-input failure can only reduce its structural query total. When
finalized marks describe a view with at most n known leaves, the cap costs
at most 8*n queries; the lower-record loop pays its separate 24*n calls. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_dfs_check_step_exact_queries (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) :
    (capDfsStep true marked control state).IsTotalQueryBound
      (capDfsStepQueries true control) := by
  cases control with
  | visit node =>
    by_cases present : marked node=true
    · simp only [capDfsStep,present,↓reduceIte,capDfsStepQueries]
      trivial
    · simp only [capDfsStep,present,↓reduceIte,capDfsStepQueries]
      trivial
  | advance node =>
    by_cases root : node=1
    · simp only [capDfsStep,if_pos root,capDfsStepQueries]
      trivial
    · by_cases even : node%2=0
      · simp only [capDfsStep,if_neg root,if_pos even,capDfsStepQueries]
        trivial
      · simp only [capDfsStep,if_neg root,if_neg even,↓reduceIte,capDfsStepQueries]
        unfold capCheckCompression
        erw [isTotalQueryBound_query_bind_iff]
        exact ⟨by decide,fun _ => by trivial⟩
  | done =>
    simp only [capDfsStep,capDfsStepQueries]
    trivial

theorem cap_check_dfs_finish_structural_queries (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    (capCheckDfsFinish marked count control state).IsTotalQueryBound
      (capDfsQueryTotal true marked count control) := by
  induction count generalizing control state with
  | zero => trivial
  | succ count ih =>
    rw [capCheckDfsFinish]
    split
    · trivial
    · rw [capDfsQueryTotal]
      apply isTotalQueryBound_bind (cap_dfs_check_step_exact_queries marked control state)
      intro next
      simpa only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff] using
        ih (capControlStep marked control) next

theorem cap_check_dfs_finish_view_queries (marked : Nat → Bool)
    (view : CapView 8) (marks : CapViewMarks marked 1 view) (state : MachineState) :
    (capCheckDfsFinish marked 1022 (.visit 1) state).IsTotalQueryBound (capCalls view) := by
  simpa only [cap_root_query_count marked view marks] using
    cap_check_dfs_finish_structural_queries marked 1022 (.visit 1) state

theorem cap_check_dfs_finish_card_queries (marked : Nat → Bool)
    (view : CapView 8) (marks : CapViewMarks marked 1 view)
    (count : Nat) (known : capMarkedCount view≤count) (state : MachineState) :
    (capCheckDfsFinish marked 1022 (.visit 1) state).IsTotalQueryBound (8*count) :=
  (cap_check_dfs_finish_view_queries marked view marks state).mono
    ((cap_calls_bound view).trans (Nat.mul_le_mul_left 8 known))

end CommitGolfCandidate
