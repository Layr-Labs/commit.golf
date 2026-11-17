import CommitGolfCandidate.CapCheckDfsReady

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute

def capCheckDfsContinue (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → Nat → Bool → OracleComp World Execution
  | 0,_,state,fuel,allowCoins => execute (capWalkImage true) fuel state allowCoins
  | count+1,control,state,fuel,allowCoins =>
      if capCheckDfsShort marked control state then
        pure ⟨.failure,capCheckExitState (capUnknownCheckGuard state) false,9,0⟩
      else do
        let next ← capDfsStep true marked control state
        let result ← capCheckDfsContinue marked count (capControlStep marked control) next
          (fuel-capDfsStepInstructions true marked control) allowCoins
        return result.charge (capDfsStepCycles true marked control)
          (capDfsStepQueries true control)

theorem cap_check_dfs_continue_execute (limit : Nat) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (fuel : Nat) (sufficient : 17*count ≤ fuel) (allowCoins : Bool) :
    execute (capWalkImage true) fuel state allowCoins =
      capCheckDfsContinue marked count control state fuel allowCoins := by
  induction count generalizing control state fuel with
  | zero => rfl
  | succ count ih =>
      cases short : capCheckDfsShort marked control state
      · have instructionBound := cap_dfs_step_instruction_bound true marked control
        have head := cap_check_dfs_ready_execute limit marked control state ready short
          (fuel-capDfsStepInstructions true marked control) allowCoins
        have headFuel :
            capDfsStepInstructions true marked control +
              (fuel-capDfsStepInstructions true marked control)=fuel := by omega
        rw [headFuel] at head
        rw [head]
        simp only [capCheckDfsContinue,short,Bool.false_eq_true,↓reduceIte]
        apply bind_congr_of_forall_mem_support
        intro next reached
        have nextReady := cap_check_dfs_ready_transport limit marked control state next
          ready short reached
        rw [ih (capControlStep marked control) next nextReady
          (fuel-capDfsStepInstructions true marked control) (by omega)]
      · have head := cap_check_dfs_short_execute limit marked control state ready short
          (fuel-9) allowCoins
        have headFuel : 9+(fuel-9)=fuel := by omega
        rw [headFuel] at head
        simpa only [capCheckDfsContinue,short,↓reduceIte] using head

end CommitGolfCandidate
