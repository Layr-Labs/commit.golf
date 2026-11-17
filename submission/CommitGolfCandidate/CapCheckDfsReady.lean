import CommitGolfCandidate.CapCheckCursorWindow
import CommitGolfCandidate.CapCheckExit

/-! Reachable checker traversal states and the actual short-proof alternative.
The proof end is the full byte length, including malformed partial digest
tails. Successful steps transport the bounded natural cursor; a short unknown
visit executes the real guard and failure halt before any proof load. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckDfsShort (marked : Nat → Bool) (control : CapDfsControl)
    (state : MachineState) : Bool :=
  match control with
  | .visit node =>
      if marked node then false
      else decide ((state.getReg .x22).toNat < (state.getReg .x25).toNat + 32)
  | _ => false

structure CapCheckDfsReady (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) : Prop where
  physical : CapDfsStateControl true state control
  valid : CapDfsControlValid control
  stable : CapDfsStable true state 12288
  marks : CapMarksReady state 256 0 marked
  window : CapCheckCursorWindow limit state

theorem cap_check_dfs_not_short_enough (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (notShort : capCheckDfsShort marked control state = false) :
    capCheckBoundaryEnough marked control state := by
  intro node atNode absent
  subst control
  simp only [capCheckDfsShort,absent,Bool.false_eq_true,↓reduceIte,
    decide_eq_false_iff_not] at notShort
  omega

theorem cap_check_dfs_ready_transport (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state next : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (notShort : capCheckDfsShort marked control state = false)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    CapCheckDfsReady limit marked (capControlStep marked control) next := by
  have enough := cap_check_dfs_not_short_enough marked control state notShort
  have access (node : Nat) (atNode : control = .visit node) (absent : marked node = false) :
      CapDfsBoundaryReady true state 12288 node := by
    have bounded : node < 512 := by
      have valid := ready.valid
      rw [atNode] at valid
      exact valid.2
    exact cap_check_boundary_ready marked control state limit ready.window enough
      node atNode absent bounded
  have transported := cap_dfs_step_support true marked control state next 12288
    ready.physical ready.valid ready.stable ready.marks (fun _ => rfl) access reached
  exact ⟨transported.1,cap_control_step_valid marked control ready.valid,
    transported.2.1,transported.2.2,
    cap_check_cursor_window_transport marked control state next limit ready.window
      (cap_check_cursor_space marked control state limit ready.window enough) reached⟩

theorem cap_check_dfs_ready_execute (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (notShort : capCheckDfsShort marked control state = false)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true)
        (capDfsStepInstructions true marked control + fuel) state allowCoins =
      (do let next ← capDfsStep true marked control state
          let result ← execute (capWalkImage true) fuel next allowCoins
          return result.charge (capDfsStepCycles true marked control)
            (capDfsStepQueries true control)) := by
  apply cap_dfs_step_execute true marked control state 12288
    ready.physical ready.valid ready.stable ready.marks (fun _ => rfl)
  intro node atNode absent
  have bounded : node < 512 := by
    have valid := ready.valid
    rw [atNode] at valid
    exact valid.2
  exact cap_check_boundary_ready marked control state limit ready.window
    (cap_check_dfs_not_short_enough marked control state notShort) node atNode absent bounded

theorem cap_check_dfs_short_execute (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (short : capCheckDfsShort marked control state = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (9 + fuel) state allowCoins =
      pure ⟨.failure,capCheckExitState (capUnknownCheckGuard state) false,9,0⟩ := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capCheckDfsShort,present,↓reduceIte] at short
        contradiction
      · have absent := Bool.eq_false_iff.mpr present
        have small := cap_check_cursor_no_wrap limit state ready.window
        have numeric : limit < (state.getReg .x25).toNat + 32 := by
          simp only [capCheckDfsShort,absent,Bool.false_eq_true,↓reduceIte,
            decide_eq_true_eq] at short
          rw [ready.window.endPointer] at short
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.2] at short
          exact short
        exact cap_unknown_check_short_reject state node (state.getReg .x25).toNat limit
          ready.physical.1 ready.stable.marks ready.physical.2 ready.valid.1 ready.valid.2
          marked ready.marks absent (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
          ready.window.endPointer
          small.1 small.2 numeric fuel allowCoins
  | advance node =>
      simp only [capCheckDfsShort] at short
      contradiction
  | done =>
      simp only [capCheckDfsShort] at short
      contradiction

end CommitGolfCandidate
