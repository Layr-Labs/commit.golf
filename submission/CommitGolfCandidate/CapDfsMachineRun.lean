import CommitGolfCandidate.CapDfsRun

/-! Actual-image instantiation of the bounded macro composition. The remaining
caller hook is explicit: construct boundary access witnesses from the cursor
invariant and preserve that invariant for every reply. All fetch/execution,
control, selector and occupancy facts are discharged by the actual bridges.
This is not yet the ABI or root/byte semantic refinement. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapDfsMachineReady (checking : Bool) (marked : Nat → Bool) (rootBase : Nat)
    (CursorInvariant : CapDfsControl → MachineState → Prop)
    (control : CapDfsControl) (state : MachineState) : Prop where
  physical : CapDfsStateControl checking state control
  valid : CapDfsControlValid control
  stable : CapDfsStable checking state rootBase
  marks : CapMarksReady state 256 0 marked
  cursor : CursorInvariant control state

theorem cap_dfs_machine_transport (checking : Bool) (marked : Nat → Bool)
    (rootBase : Nat) (CursorInvariant : CapDfsControl → MachineState → Prop)
    (checkBase : checking = true → rootBase = 12288)
    (access : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ node, control = .visit node → marked node = false →
        CapDfsBoundaryReady checking state rootBase node)
    (cursorTransport : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ next ∈ support (capDfsStep checking marked control state),
        CursorInvariant (capControlStep marked control) next)
    (control : CapDfsControl) (state next : MachineState)
    (ready : CapDfsMachineReady checking marked rootBase CursorInvariant control state)
    (reached : next ∈ support (capDfsStep checking marked control state)) :
    CapDfsMachineReady checking marked rootBase CursorInvariant
      (capControlStep marked control) next := by
  have transported := cap_dfs_step_support checking marked control state next rootBase
    ready.physical ready.valid ready.stable ready.marks checkBase
    (access control state ready) reached
  exact ⟨transported.1, cap_control_step_valid marked control ready.valid,
    transported.2.1, transported.2.2, cursorTransport control state ready next reached⟩

theorem cap_dfs_machine_run_execute (checking : Bool) (marked : Nat → Bool)
    (rootBase : Nat) (CursorInvariant : CapDfsControl → MachineState → Prop)
    (checkBase : checking = true → rootBase = 12288)
    (access : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ node, control = .visit node → marked node = false →
        CapDfsBoundaryReady checking state rootBase node)
    (cursorTransport : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ next ∈ support (capDfsStep checking marked control state),
        CursorInvariant (capControlStep marked control) next)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (ready : CapDfsMachineReady checking marked rootBase CursorInvariant control state)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking)
        (capDfsInstructionTotal checking marked count control + fuel) state allowCoins =
      (do let final ← capDfsRun checking marked count control state
          let result ← execute (capWalkImage checking) fuel final allowCoins
          return result.charge (capDfsCycleTotal checking marked count control)
            (capDfsQueryTotal checking marked count control)) := by
  apply cap_dfs_run_execute checking marked (capWalkImage checking)
    (CapDfsMachineReady checking marked rootBase CursorInvariant)
  · intro nextControl nextState nextReady nextFuel nextAllowCoins
    exact cap_dfs_step_execute checking marked nextControl nextState rootBase
      nextReady.physical nextReady.valid nextReady.stable nextReady.marks
      checkBase (access nextControl nextState nextReady) nextFuel nextAllowCoins
  · intro nextControl nextState nextReady next reached
    exact cap_dfs_machine_transport checking marked rootBase CursorInvariant
      checkBase access cursorTransport nextControl nextState next nextReady reached
  · exact ready

/-- With the cursor/access hooks established, every reply sequence reaches
the actual root-completion PC within the structural 1022-macro allowance. -/
theorem cap_dfs_machine_run_done (checking : Bool) (marked : Nat → Bool)
    (rootBase : Nat) (CursorInvariant : CapDfsControl → MachineState → Prop)
    (checkBase : checking = true → rootBase = 12288)
    (access : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ node, control = .visit node → marked node = false →
        CapDfsBoundaryReady checking state rootBase node)
    (cursorTransport : ∀ control state,
      CapDfsMachineReady checking marked rootBase CursorInvariant control state →
      ∀ next ∈ support (capDfsStep checking marked control state),
        CursorInvariant (capControlStep marked control) next)
    (state final : MachineState)
    (ready : CapDfsMachineReady checking marked rootBase CursorInvariant (.visit 1) state)
    (reached : final ∈ support (capDfsRun checking marked 1022 (.visit 1) state)) :
    final.pc = capAdvanceDone checking ∧
      CapDfsStable checking final rootBase ∧ CapMarksReady final 256 0 marked ∧
      CursorInvariant .done final := by
  have finished := cap_dfs_run_support checking marked
    (CapDfsMachineReady checking marked rootBase CursorInvariant)
    (fun control state ready next reached =>
      cap_dfs_machine_transport checking marked rootBase CursorInvariant
        checkBase access cursorTransport control state next ready reached)
    1022 (.visit 1) state final ready reached
  rw [cap_control_complete] at finished
  exact ⟨finished.physical, finished.stable, finished.marks, finished.cursor⟩

end CommitGolfCandidate
