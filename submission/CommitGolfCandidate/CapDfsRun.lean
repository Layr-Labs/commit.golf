import CommitGolfCandidate.CapDfsStepSupport
import CommitGolfCandidate.CapDfsCostBound

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capDfsRun (checking : Bool) (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → OracleComp World MachineState
  | 0, _, state => pure state
  | count + 1, control, state => do
      let next ← capDfsStep checking marked control state
      capDfsRun checking marked count (capControlStep marked control) next

private theorem charge_pair (result : Execution) (first second callsFirst callsSecond : Nat) :
    (result.charge first callsFirst).charge second callsSecond =
      result.charge (second + first) (callsSecond + callsFirst) := by
  simp only [Execution.charge, Nat.add_assoc]

private theorem charge_zero (result : Execution) : result.charge 0 0 = result := by
  simp only [Execution.charge, Nat.zero_add]

theorem cap_dfs_run_execute (checking : Bool) (marked : Nat → Bool) (image : Image)
    (Invariant : CapDfsControl → MachineState → Prop)
    (checked : ∀ control state, Invariant control state → ∀ fuel allowCoins,
      execute image (capDfsStepInstructions checking marked control + fuel) state allowCoins =
        (do let next ← capDfsStep checking marked control state
            let result ← execute image fuel next allowCoins
            return result.charge (capDfsStepCycles checking marked control)
              (capDfsStepQueries checking control)))
    (transport : ∀ control state, Invariant control state →
      ∀ next ∈ support (capDfsStep checking marked control state),
        Invariant (capControlStep marked control) next)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (ready : Invariant control state) (fuel : Nat) (allowCoins : Bool) :
    execute image (capDfsInstructionTotal checking marked count control + fuel)
        state allowCoins =
      (do let final ← capDfsRun checking marked count control state
          let result ← execute image fuel final allowCoins
          return result.charge (capDfsCycleTotal checking marked count control)
            (capDfsQueryTotal checking marked count control)) := by
  induction count generalizing control state with
  | zero =>
      simp only [capDfsInstructionTotal, capDfsCycleTotal, capDfsQueryTotal,
        capDfsRun, Nat.zero_add, pure_bind, charge_zero]
      exact (bind_pure _).symm
  | succ count ih =>
      rw [capDfsInstructionTotal, Nat.add_assoc, checked control state ready]
      calc
        _ = (do
          let next ← capDfsStep checking marked control state
          let result ← (do
            let final ← capDfsRun checking marked count (capControlStep marked control) next
            let result ← execute image fuel final allowCoins
            return result.charge
              (capDfsCycleTotal checking marked count (capControlStep marked control))
              (capDfsQueryTotal checking marked count (capControlStep marked control)))
          return result.charge (capDfsStepCycles checking marked control)
            (capDfsStepQueries checking control)) := by
              apply bind_congr_of_forall_mem_support
              intro next reached
              rw [ih (capControlStep marked control) next
                (transport control state ready next reached)]
        _ = _ := by
          simp only [capDfsRun, capDfsCycleTotal, capDfsQueryTotal, bind_assoc,
            pure_bind, charge_pair]

theorem cap_dfs_run_support (checking : Bool) (marked : Nat → Bool)
    (Invariant : CapDfsControl → MachineState → Prop)
    (transport : ∀ control state, Invariant control state →
      ∀ next ∈ support (capDfsStep checking marked control state),
        Invariant (capControlStep marked control) next)
    (count : Nat) (control : CapDfsControl) (state final : MachineState)
    (ready : Invariant control state)
    (reached : final ∈ support (capDfsRun checking marked count control state)) :
    Invariant (capControlRun marked count control) final := by
  induction count generalizing control state with
  | zero =>
      have same := eq_of_mem_support_pure state reached
      subst final
      exact ready
  | succ count ih =>
      rw [capDfsRun] at reached
      obtain ⟨next, nextReached, tailReached⟩ := mem_support_bind_peel _ _ reached
      exact ih (capControlStep marked control) next
        (transport control state ready next nextReached) tailReached

end CommitGolfCandidate
