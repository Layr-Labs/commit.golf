import CommitGolfCandidate.CapCheckRecordsAdmission
import CommitGolfCandidate.CapCheckRecordExecution

/-! The actual outer record loop with a uniform sufficient fuel reserve.
Only consumed instructions are subtracted. A duplicate mismatch halts
immediately; successful exhaustion invokes the real mark-pass continuation.
The latter is deliberately retained as execute here, not a fictitious halt. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute capCheckRecordNextPrefix

def capCheckRecordsContinue : Nat → MachineState → Nat → Bool → OracleComp World Execution
  | 0,state,fuel,allowCoins => execute (capProgram.image .check) fuel state allowCoins
  | count+1,state,fuel,allowCoins => do
      let lower ← capCheckLowerRecord state
      if (capCheckGroupResult lower).2 then
        let result ← capCheckRecordsContinue count (capCheckRecordResult lower).1
          (fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3) allowCoins
        return result.charge
          (capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 16+
            231+capCheckGroupSteps lower+3) 18
      else pure ⟨.failure,(capCheckGroupResult lower).1,
        capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 16+
          231+capCheckGroupSteps lower,18⟩

theorem cap_check_records_execute (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (ordinal count : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal count state)
    (fuel : Nat) (sufficient : 671*count ≤ fuel) (allowCoins : Bool) :
    execute (capProgram.image .check) fuel state allowCoins =
      capCheckRecordsContinue count state fuel allowCoins := by
  induction count generalizing ordinal state fuel with
  | zero => rfl
  | succ count ih =>
    obtain ⟨index,bounded,loaded⟩ :=
      cap_check_records_ready_index input ordinal (count+1) state ready (by omega)
    have access := cap_check_records_ready_admission input ordinal (count+1)
      state ready (by omega) admitted enough
    have pc : state.pc=4212 := by
      rw [ready.pc,if_neg (by omega)]
    have lowerBound := cap_check_lower_record_steps_bound state
    have head := cap_check_record_execute state index bounded loaded pc ready.scratch
      ready.leaves ready.marks ready.roots ready.one access.1 access.2.1
      access.2.2.1 access.2.2.2 (fuel-671) allowCoins
    have headFuel : 671+(fuel-671)=fuel := by omega
    rw [headFuel] at head
    change execute (capProgram.image .check) fuel state allowCoins = _ at head
    rw [head]
    unfold capCheckRecordsContinue
    apply bind_congr_of_forall_mem_support
    intro lower reachable
    have groupBound := cap_check_group_steps_bound lower
    have remainder :
        671-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3+(fuel-671) =
        fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3 := by omega
    cases passed : (capCheckGroupResult lower).2
    · simp only [Bool.false_eq_true,↓reduceIte]
    · simp only [↓reduceIte]
      have recordReachable : capCheckRecordResult lower ∈ support (capCheckRecordRun state) :=
        (cap_check_record_run_support _ _).mpr ⟨lower,reachable,rfl⟩
      have recordPassed : (capCheckRecordResult lower).2=true := by
        rw [cap_check_record_result_passed,passed]
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        (capCheckRecordResult lower) recordReachable recordPassed
      have next := ih (ordinal+1) _ nextReady
        (fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3) (by omega)
      change execute ((capExperimental 24).image .check)
        (fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3)
        (capCheckRecordResult lower).1 allowCoins = _ at next
      rw [remainder,next]

end CommitGolfCandidate
