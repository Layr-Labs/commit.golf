import CommitGolfCandidate.CapCheckRootHalt

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckFinalResult (state : MachineState) : Execution :=
  if state.getReg .x25=state.getReg .x22 then
    (capCheckRootResult (capCheckProofEndState state)).charge 1 0
  else ⟨.failure,capCheckExitState (capCheckProofEndState state) false,4,0⟩

theorem cap_check_final_execute (state : MachineState) (pc : state.pc=4736)
    (rootValid : ∀ i < 4, accessValid
      (state.getReg .x18+signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true)
    (commitmentValid : ∀ i < 4, accessValid
      (state.getReg .x26+signExtend12 (BitVec.ofNat 12 (8*i))) 8=true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (17+fuel) state allowCoins=
      pure (capCheckFinalResult state) := by
  by_cases exhausted : state.getReg .x25=state.getReg .x22
  · have endPC := cap_check_proof_end_pc state pc
    rw [if_pos exhausted] at endPC
    have nextRoot (i : Nat) (inside : i<4) :
        accessValid ((capCheckProofEndState state).getReg .x18+
          signExtend12 (BitVec.ofNat 12 (32+8*i))) 8=true := by
      rw [cap_check_proof_end_register]
      exact rootValid i inside
    have nextCommitment (i : Nat) (inside : i<4) :
        accessValid ((capCheckProofEndState state).getReg .x26+
          signExtend12 (BitVec.ofNat 12 (8*i))) 8=true := by
      rw [cap_check_proof_end_register]
      exact commitmentValid i inside
    rw [show 17+fuel=1+(16+fuel) by omega,cap_check_proof_end_execute state pc,
      cap_check_root_halt _ endPC nextRoot nextCommitment]
    simp only [pure_bind,capCheckFinalResult,if_pos exhausted]
  · have failed := cap_check_proof_end_reject state pc exhausted (13+fuel) allowCoins
    rw [show 4+(13+fuel)=17+fuel by omega] at failed
    simpa only [capCheckFinalResult,if_neg exhausted] using failed

theorem cap_check_final_cycles (state : MachineState) :
    (capCheckFinalResult state).cycles≤17 := by
  have rootBound := cap_check_root_result_cycles (capCheckProofEndState state)
  unfold capCheckFinalResult
  split <;> simp only [Execution.charge] <;> omega

theorem cap_check_final_queries (state : MachineState) :
    (capCheckFinalResult state).oracleCalls=0 := by
  unfold capCheckFinalResult
  split
  · simp only [Execution.charge,Nat.zero_add,cap_check_root_result_queries]
  · rfl

end CommitGolfCandidate
