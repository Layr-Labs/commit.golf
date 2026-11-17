import CommitGolfCandidate.CapCheckRecordRun

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute capCheckRecordNextPrefix capCheckGroupStartPrefix

private theorem record_success_charge (computation : OracleComp World Execution)
    (lowerCycles groupSteps : Nat) :
    (do
      let result ← computation
      return ((result.charge 3 0).charge groupSteps 0).charge lowerCycles 24) =
    (do let result ← computation
        return result.charge (lowerCycles+groupSteps+3) 24) := by
  simp [Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem cap_check_record_execute (state : MachineState) (index : Nat)
    (bounded : index < 2^24)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (pc : state.pc = 4212) (scratch : state.getReg .x21 = 256)
    (leaves : state.getReg .x19 = 256) (marks : state.getReg .x9 = 28672)
    (roots : state.getReg .x18 = 12288) (one : state.getReg .x31 = 1)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25+BitVec.ofNat 64 (8*word.val)) 8 = true)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8+BitVec.ofNat 64 (8*word)) 8 = true)
    (siblingsValid : ∀ word < 64,
      accessValid (state.getReg .x25+32+BitVec.ofNat 64 (8*word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (671+fuel) state allowCoins =
      (do
        let lower ← capCheckLowerRecord state
        if (capCheckGroupResult lower).2 then
          let result ← execute ((capExperimental 24).image .check)
            (671-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3+fuel)
            (capCheckRecordResult lower).1 allowCoins
          return result.charge
            (capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 16+
              321+capCheckGroupSteps lower+3) 24
        else pure ⟨.failure,(capCheckGroupResult lower).1,
          capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 16+
            321+capCheckGroupSteps lower,24⟩) := by
  have lowerBound := cap_check_lower_record_steps_bound state
  rw [show 671+fuel=capCheckLowerRecordSteps state+
      (671-capCheckLowerRecordSteps state+fuel) by omega,
    cap_check_lower_record_execute state pc scratch indexValid saltValid sourceValid siblingsValid]
  apply bind_congr_of_forall_mem_support
  intro lower reachable
  have ready := cap_check_lower_group_ready state lower index bounded loaded scratch
    leaves marks roots one reachable
  have admitted := cap_check_group_ready_admission lower (index/2^16) ready
  have groupBound := cap_check_group_steps_bound lower
  rw [show 671-capCheckLowerRecordSteps state+fuel =
      capCheckGroupSteps lower+
        (671-capCheckLowerRecordSteps state-capCheckGroupSteps lower+fuel) by omega,
    cap_check_group_run_execute lower ready.pc admitted.1 admitted.2.1
      admitted.2.2.1 admitted.2.2.2]
  cases passed : (capCheckGroupResult lower).2
  · simp [Bool.false_eq_true,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  · have groupPC := cap_check_group_result_pc lower passed
    rw [show 671-capCheckLowerRecordSteps state-capCheckGroupSteps lower+fuel =
        3+(671-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3+fuel) by omega,
      cap_check_record_next_execute _ groupPC]
    simp only [bind_assoc,pure_bind,capCheckRecordResult,passed,↓reduceIte]
    exact record_success_charge _ _ _

end CommitGolfCandidate
