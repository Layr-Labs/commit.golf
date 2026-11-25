import CommitGolfCandidate.CapCheckRootFinish

/-! The final root comparison is a real terminating checker computation.
Its sixteen-instruction fuel reserve includes all four comparisons, the
success jump and halt. Mismatches retain their smaller actual early-exit cost. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckRootResult (state : MachineState) : Execution :=
  if (capCheckRootLoop state 0 4).2 then
    ⟨.success,capCheckExitState (capCheckRootDone state) true,16,0⟩
  else
    ⟨.failure,capCheckExitState (capCheckRootLoop state 0 4).1 false,
      capCheckRootSteps state 0 4+3,0⟩

theorem cap_check_root_halt (state : MachineState) (pc : state.pc=4740)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true)
    (commitmentValid : ∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8=true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (16+fuel) state allowCoins =
      pure (capCheckRootResult state) := by
  change execute ((capExperimental 24).image .check) (16+fuel) state allowCoins=_
  cases passed : (capCheckRootLoop state 0 4).2
  · have bounded := cap_check_root_steps_bound state 0 4
    have head := cap_check_root_fail_execute state pc passed rootValid commitmentValid
      (16-capCheckRootSteps state 0 4-3+fuel) allowCoins
    have sufficient :
        capCheckRootSteps state 0 4+3+
          (16-capCheckRootSteps state 0 4-3+fuel)=16+fuel := by omega
    rw [sufficient] at head
    simpa only [capCheckRootResult,passed,Bool.false_eq_true,↓reduceIte] using head
  · have endPC := cap_check_root_done_pc state pc passed
    rw [show 16+fuel=13+(3+fuel) by omega,
      cap_check_root_pass_execute state pc passed rootValid commitmentValid]
    change (do
      let result ← execute (capWalkImage true) (3+fuel) (capCheckRootDone state) allowCoins
      return result.charge 13 0) = _
    rw [cap_check_exit _ true endPC]
    simp only [pure_bind,capCheckRootResult,passed,↓reduceIte,Execution.charge]

theorem cap_check_root_result_cycles (state : MachineState) :
    (capCheckRootResult state).cycles≤16 := by
  have bounded := cap_check_root_steps_bound state 0 4
  unfold capCheckRootResult
  split <;> simp only <;> omega

theorem cap_check_root_result_queries (state : MachineState) :
    (capCheckRootResult state).oracleCalls=0 := by
  unfold capCheckRootResult
  split <;> rfl

end CommitGolfCandidate
