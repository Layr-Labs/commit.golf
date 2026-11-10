import CommitGolfCandidate.CapCheckDfsExecution

/-! A pure checker traversal phase result with actual short-input failure.
Successful exhaustion is the real root-comparison entry, not acceptance.
The coarse all-reply query ceiling is only a termination aid; the eventual
100-per-record budget requires the finer occupied-cap semantics. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckDfsRun (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → OracleComp World (MachineState × Bool)
  | 0,_,state => pure (state,true)
  | count+1,control,state =>
      if capCheckDfsShort marked control state then
        pure (capCheckExitState (capUnknownCheckGuard state) false,false)
      else do
        let next ← capDfsStep true marked control state
        capCheckDfsRun marked count (capControlStep marked control) next

theorem cap_dfs_check_step_query_bound (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) :
    (capDfsStep true marked control state).IsTotalQueryBound 1 := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep,present,↓reduceIte]
        trivial
      · simp only [capDfsStep,present,↓reduceIte]
        trivial
  | advance node =>
      by_cases root : node=1
      · simp only [capDfsStep,if_pos root]
        trivial
      · by_cases even : node%2=0
        · simp only [capDfsStep,if_neg root,if_pos even]
          trivial
        · simp only [capDfsStep,if_neg root,if_neg even,↓reduceIte]
          unfold capCheckCompression
          erw [isTotalQueryBound_query_bind_iff]
          exact ⟨by decide,fun _ => by trivial⟩
  | done =>
      simp only [capDfsStep]
      trivial

theorem cap_check_dfs_run_queries (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    (capCheckDfsRun marked count control state).IsTotalQueryBound count := by
  induction count generalizing control state with
  | zero => trivial
  | succ count ih =>
      rw [capCheckDfsRun]
      split
      · trivial
      · have tail : ∀ next : MachineState,
            (capCheckDfsRun marked count (capControlStep marked control) next).IsTotalQueryBound
              count := fun next => ih _ next
        have total := isTotalQueryBound_bind
          (cap_dfs_check_step_query_bound marked control state) tail
        convert total using 1 <;> omega

theorem cap_check_dfs_run_ready (limit : Nat) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (result : MachineState × Bool)
    (reached : result ∈ support (capCheckDfsRun marked count control state))
    (passed : result.2=true) :
    CapCheckDfsReady limit marked (capControlRun marked count control) result.1 := by
  induction count generalizing control state with
  | zero =>
      simp only [capCheckDfsRun,support_pure,Set.mem_singleton_iff] at reached
      subst result
      exact ready
  | succ count ih =>
      rw [capCheckDfsRun] at reached
      cases short : capCheckDfsShort marked control state
      · simp only [short,Bool.false_eq_true,↓reduceIte,mem_support_bind_iff] at reached
        obtain ⟨next,nextReached,tailReached⟩ := reached
        have nextReady := cap_check_dfs_ready_transport limit marked control state next
          ready short nextReached
        exact ih (capControlStep marked control) next nextReady tailReached
      · simp only [short,↓reduceIte,support_pure,Set.mem_singleton_iff] at reached
        subst result
        contradiction

theorem cap_check_dfs_run_done (limit : Nat) (marked : Nat → Bool)
    (state : MachineState) (ready : CapCheckDfsReady limit marked (.visit 1) state)
    (result : MachineState × Bool)
    (reached : result ∈ support (capCheckDfsRun marked 510 (.visit 1) state))
    (passed : result.2=true) :
    result.1.pc=4736 ∧ CapDfsStable true result.1 12288 ∧
      CapMarksReady result.1 128 0 marked ∧ CapCheckCursorWindow limit result.1 := by
  have finished := cap_check_dfs_run_ready limit marked 510 (.visit 1)
    state ready result reached passed
  rw [cap_control_complete] at finished
  exact ⟨finished.physical,finished.stable,finished.marks,finished.window⟩

end CommitGolfCandidate
