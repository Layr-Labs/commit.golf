import CommitGolfCandidate.CapCheckDfsFrame
import CommitGolfCandidate.CapCheckFinal

/-! A terminating cap traversal with its actual root-comparison continuation.
The fuel reserve is conservative; each step charges its actual cost. Short
proofs stop before loading an absent digest. Final load admissions are carried
across arbitrary replies, rather than inferred from a successful phase flag. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute

def capCheckDfsFinish (marked : Nat → Bool) :
    Nat → CapDfsControl → MachineState → OracleComp World Execution
  | 0,_,state => pure (capCheckFinalResult state)
  | count+1,control,state =>
      if capCheckDfsShort marked control state then
        pure ⟨.failure,capCheckExitState (capUnknownCheckGuard state) false,9,0⟩
      else do
        let next ← capDfsStep true marked control state
        let result ← capCheckDfsFinish marked count (capControlStep marked control) next
        return result.charge (capDfsStepCycles true marked control)
          (capDfsStepQueries true control)

theorem cap_check_dfs_finish_execute (limit : Nat) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (complete : capControlRun marked count control=.done)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true)
    (commitmentValid : ∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8=true)
    (fuel : Nat) (sufficient : 17*count+17≤fuel) (allowCoins : Bool) :
    execute (capWalkImage true) fuel state allowCoins=
      capCheckDfsFinish marked count control state := by
  induction count generalizing control state fuel with
  | zero =>
    change control=.done at complete
    subst control
    have pc : state.pc=4736 := ready.physical
    have tail := cap_check_final_execute state pc rootValid commitmentValid
      (fuel-17) allowCoins
    rw [show 17+(fuel-17)=fuel by omega] at tail
    exact tail
  | succ count ih =>
    cases short : capCheckDfsShort marked control state
    · have instructionBound := cap_dfs_step_instruction_bound true marked control
      have head := cap_check_dfs_ready_execute limit marked control state ready short
        (fuel-capDfsStepInstructions true marked control) allowCoins
      rw [show capDfsStepInstructions true marked control+
        (fuel-capDfsStepInstructions true marked control)=fuel by omega] at head
      rw [head]
      simp only [capCheckDfsFinish,short,Bool.false_eq_true,↓reduceIte]
      apply bind_congr_of_forall_mem_support
      intro next reached
      have nextReady := cap_check_dfs_ready_transport limit marked control state next
        ready short reached
      have sameRoot : next.getReg .x18=state.getReg .x18 :=
        nextReady.stable.roots.trans ready.stable.roots.symm
      have sameClaim := cap_dfs_check_commitment_pointer marked control state next reached
      have nextRoot (i : Nat) (inside : i<4) :
          accessValid (next.getReg .x18+
            signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true := by
        rw [sameRoot]
        exact rootValid i inside
      have nextClaim (i : Nat) (inside : i<4) :
          accessValid (next.getReg .x26+
            signExtend12 (BitVec.ofNat 12 (8*i))) 8=true := by
        rw [sameClaim]
        exact commitmentValid i inside
      rw [ih (capControlStep marked control) next nextReady complete nextRoot nextClaim
        (fuel-capDfsStepInstructions true marked control) (by omega)]
    · have head := cap_check_dfs_short_execute limit marked control state ready short
        (fuel-9) allowCoins
      rw [show 9+(fuel-9)=fuel by omega] at head
      simpa only [capCheckDfsFinish,short,↓reduceIte] using head

theorem cap_check_dfs_finish_queries (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState) :
    (capCheckDfsFinish marked count control state).IsTotalQueryBound count := by
  induction count generalizing control state with
  | zero => trivial
  | succ count ih =>
    rw [capCheckDfsFinish]
    split
    · trivial
    · have tail : ∀ next : MachineState,
          (do let result ← capCheckDfsFinish marked count (capControlStep marked control) next
              return result.charge (capDfsStepCycles true marked control)
                (capDfsStepQueries true control)).IsTotalQueryBound count := by
        intro next
        simpa only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff] using ih _ next
      have total := isTotalQueryBound_bind
        (cap_dfs_check_step_query_bound marked control state) tail
      convert total using 1 <;> omega

end CommitGolfCandidate
