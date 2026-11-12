import CommitGolfCandidate.CapCheckPostRecords
import CommitGolfCandidate.CapCheckRecordsExecution

/-! Universal query budget for the actual record continuation and terminating
cap phase. The supported insertion witness bounds occupancy, so duplicates and
inconsistent arbitrary replies do not create uncharged cap groups. Failed
records halt immediately. Fuel is a reserve, not a claimed execution cost. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute capCheckLowerRecord

theorem cap_check_records_continue_budget (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (ordinal count : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (zeroSelectors : count = 0 → CapCheckSelectors state)
    (fuel : Nat) (sufficient : 671*count+19945 ≤ fuel) (allowCoins : Bool) :
    (capCheckRecordsContinue count state fuel allowCoins).IsTotalQueryBound
      (24*count+8*(capMarkedCount (capKnownView roots 8 0)+count)) := by
  induction count generalizing ordinal state roots fuel with
  | zero =>
    rw [capCheckRecordsContinue]
    have tail := cap_check_post_records_queries input ordinal state ready roots collected
      (zeroSelectors rfl) admitted enough (capMarkedCount (capKnownView roots 8 0))
      (by rfl) (fuel-2554) (by omega) allowCoins
    rw [show 2554+(fuel-2554)=fuel by omega] at tail
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] using tail
  | succ count ih =>
    rw [capCheckRecordsContinue]
    have restBound :
        24*(count+1)+8*(capMarkedCount (capKnownView roots 8 0)+(count+1)) =
        24+(24*count+8*(capMarkedCount (capKnownView roots 8 0)+1+count)) := by omega
    rw [restBound]
    apply isTotalQueryBound_bind_of_mem_support (cap_check_lower_record_query_bound state)
    intro lower reachable
    cases passed : (capCheckGroupResult lower).2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      trivial
    · simp only [↓reduceIte]
      have recordReached : capCheckRecordResult lower ∈ support (capCheckRecordRun state) :=
        (cap_check_record_run_support _ _).mpr ⟨lower, reachable, rfl⟩
      have recordPassed : (capCheckRecordResult lower).2 = true := by
        rw [cap_check_record_result_passed, passed]
      obtain ⟨next, nextCollected, nextCount⟩ :=
        cap_check_record_supported_count input ordinal count state ready roots collected
          (capCheckRecordResult lower) recordReached recordPassed
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        (capCheckRecordResult lower) recordReached recordPassed
      have selectors := cap_check_record_run_selectors state (capCheckRecordResult lower)
        recordReached recordPassed
      have lowerBound := cap_check_lower_record_steps_bound state
      have groupBound := cap_check_group_steps_bound lower
      have tail := ih (ordinal+1) (capCheckRecordResult lower).1 nextReady next
        nextCollected (fun _ => selectors)
        (fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3) (by omega)
      have enlarged := tail.mono (show
        24*count+8*(capMarkedCount (capKnownView next 8 0)+count) ≤
        24*count+8*(capMarkedCount (capKnownView roots 8 0)+1+count) by omega)
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using enlarged

theorem cap_check_nonempty_continue_budget (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (nonempty : 0 < input.positions.card)
    (fuel : Nat) (sufficient : 671*input.positions.card+19945 ≤ fuel)
    (allowCoins : Bool) :
    (execute (capProgram.image .check) fuel
      (capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input)))
      allowCoins).IsTotalQueryBound (32*input.positions.card) := by
  let state := capCheckRecordEntry (capCheckLengthState (capProgram.initialState .check input))
  have ready := cap_check_records_ready_initial input nonempty
  rw [cap_check_records_execute input admitted enough 0 input.positions.card state ready
    fuel (by omega) allowCoins]
  have bound := cap_check_records_continue_budget input admitted enough 0
    input.positions.card state ready (fun _ => none)
    (cap_check_collected_initial input) (fun zero => by omega) fuel sufficient allowCoins
  have empty : capMarkedCount (capKnownView (fun _ => none) 8 0) = 0 := by
    rw [cap_known_view_card]
    simp
  have total : 32*input.positions.card =
      24*input.positions.card+
        8*(capMarkedCount (capKnownView (fun _ => none) 8 0)+input.positions.card) := by
    rw [empty]
    omega
  rw [total]
  exact bound

end CommitGolfCandidate
