import CommitGolfCandidate.CapCheckProgramBudget

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute capCheckLowerRecord

theorem cap_check_final_terminated (state : MachineState) :
    (capCheckFinalResult state).exit ≠ .unfinished := by
  unfold capCheckFinalResult capCheckRootResult
  split
  · split <;> simp only [Execution.charge] <;> decide
  · change Exit.failure ≠ Exit.unfinished
    decide

theorem cap_check_dfs_finish_terminated (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state : MachineState)
    (result : Execution)
    (reached : result ∈ support (capCheckDfsFinish marked count control state)) :
    result.exit ≠ .unfinished := by
  induction count generalizing control state result with
  | zero =>
    simp only [capCheckDfsFinish,support_pure,Set.mem_singleton_iff] at reached
    subst result
    exact cap_check_final_terminated state
  | succ count ih =>
    rw [capCheckDfsFinish] at reached
    split at reached
    · simp only [support_pure,Set.mem_singleton_iff] at reached
      subst result
      change Exit.failure ≠ Exit.unfinished
      decide
    · obtain ⟨next,_,tailReached⟩ :=
        (mem_support_bind_iff _ _ _).mp reached
      obtain ⟨finished,finishedReached,returned⟩ :=
        (mem_support_bind_iff _ _ _).mp tailReached
      simp only [support_pure,Set.mem_singleton_iff] at returned
      subst result
      exact ih (capControlStep marked control) next finished finishedReached

theorem cap_check_post_records_terminated (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (fuel : Nat) (sufficient : 19945 ≤ fuel) (allowCoins : Bool)
    (result : Execution)
    (reached : result ∈ support
      (execute (capProgram.image .check) fuel state allowCoins)) :
    result.exit ≠ .unfinished := by
  have execution := cap_check_post_records_execute input ordinal state ready roots collected
    selectors admitted enough (fuel-2554) (by omega) allowCoins
  rw [show 2554+(fuel-2554)=fuel by omega] at execution
  rw [execution] at reached
  obtain ⟨finished,finishedReached,returned⟩ :=
    (mem_support_bind_iff _ _ _).mp reached
  simp only [support_pure,Set.mem_singleton_iff] at returned
  subst result
  exact cap_check_dfs_finish_terminated _ _ _ _ finished finishedReached

theorem cap_check_records_continue_terminated (input : CheckInput)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 544*input.positions.card ≤ input.proof.length)
    (ordinal count : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal count state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (zeroSelectors : count=0 → CapCheckSelectors state)
    (fuel : Nat) (sufficient : 671*count+19945 ≤ fuel) (allowCoins : Bool)
    (result : Execution)
    (reached : result ∈ support (capCheckRecordsContinue count state fuel allowCoins)) :
    result.exit ≠ .unfinished := by
  induction count generalizing ordinal state roots fuel result with
  | zero =>
    exact cap_check_post_records_terminated input admitted enough ordinal state ready
      roots collected (zeroSelectors rfl) fuel (by omega) allowCoins result reached
  | succ count ih =>
    rw [capCheckRecordsContinue] at reached
    obtain ⟨lower,lowerReached,returned⟩ :=
      (mem_support_bind_iff _ _ _).mp reached
    cases passed : (capCheckGroupResult lower).2
    · simp only [passed,Bool.false_eq_true,↓reduceIte,support_pure,
        Set.mem_singleton_iff] at returned
      subst result
      change Exit.failure ≠ Exit.unfinished
      decide
    · simp only [passed,↓reduceIte] at returned
      obtain ⟨finished,finishedReached,charged⟩ :=
        (mem_support_bind_iff _ _ _).mp returned
      simp only [support_pure,Set.mem_singleton_iff] at charged
      subst result
      have recordReached : capCheckRecordResult lower ∈ support (capCheckRecordRun state) :=
        (cap_check_record_run_support _ _).mpr ⟨lower,lowerReached,rfl⟩
      have recordPassed : (capCheckRecordResult lower).2=true := by
        rw [cap_check_record_result_passed,passed]
      obtain ⟨next,nextCollected,_⟩ :=
        cap_check_record_supported_count input ordinal count state ready roots collected
          (capCheckRecordResult lower) recordReached recordPassed
      have nextReady := cap_check_records_ready_next input ordinal count state ready
        (capCheckRecordResult lower) recordReached recordPassed
      have selectors := cap_check_record_run_selectors state (capCheckRecordResult lower)
        recordReached recordPassed
      have lowerBound := cap_check_lower_record_steps_bound state
      have groupBound := cap_check_group_steps_bound lower
      exact ih (ordinal+1) (capCheckRecordResult lower).1 nextReady next nextCollected
        (fun _ => selectors)
        (fuel-capCheckLowerRecordSteps state-capCheckGroupSteps lower-3) (by omega)
        finished finishedReached

theorem cap_check_program_terminated (input : CheckInput) (result : Execution)
    (reached : result ∈ support (capProgram.run .check input)) :
    result.exit ≠ .unfinished := by
  by_cases admitted : input.proof.length ≤ capProgram.sizes.proof
  · change result ∈ support (if decide (input.proof.length ≤ capProgram.sizes.proof) then
        execute (capProgram.image .check) (capProgram.steps .check)
          (capProgram.initialState .check input) false
      else pure ⟨.failure,initialMachine,0,0⟩) at reached
    simp only [admitted,decide_true,ite_true] at reached
    have sufficient := cap_check_program_fuel input
    by_cases enough : 544*input.positions.card ≤ input.proof.length
    · by_cases empty : input.positions.card=0
      · have execution := cap_check_input_empty input admitted empty
          (capProgram.steps .check-16) false
        rw [show 16+(capProgram.steps .check-16)=capProgram.steps .check by omega]
          at execution
        rw [execution] at reached
        simp only [support_pure,Set.mem_singleton_iff] at reached
        subst result
        change (if input.proof.length=0 then Exit.success else Exit.failure) ≠ Exit.unfinished
        split <;> decide
      · have execution := cap_check_input_nonempty input admitted enough (by omega)
          (capProgram.steps .check-29) false
        rw [show 29+(capProgram.steps .check-29)=capProgram.steps .check by omega]
          at execution
        rw [execution] at reached
        obtain ⟨finished,finishedReached,returned⟩ :=
          (mem_support_bind_iff _ _ _).mp reached
        simp only [support_pure,Set.mem_singleton_iff] at returned
        subst result
        let state := capCheckRecordEntry
          (capCheckLengthState (capProgram.initialState .check input))
        have ready := cap_check_records_ready_initial input (by omega)
        rw [cap_check_records_execute input admitted enough 0 input.positions.card
          state ready (capProgram.steps .check-29) (by omega) false] at finishedReached
        exact cap_check_records_continue_terminated input admitted enough 0
          input.positions.card state ready (fun _ => none) (cap_check_collected_initial input)
          (fun zero => False.elim (empty zero)) (capProgram.steps .check-29) (by omega) false
          finished finishedReached
    · have execution := cap_check_short_reject input admitted (by omega)
        (capProgram.steps .check-14) false
      rw [show 14+(capProgram.steps .check-14)=capProgram.steps .check by omega] at execution
      rw [execution] at reached
      simp only [support_pure,Set.mem_singleton_iff] at reached
      subst result
      change Exit.failure ≠ Exit.unfinished
      decide
  · simp only [Submission.run,admitted,decide_false,ite_false,support_pure,
      Set.mem_singleton_iff] at reached
    subst result
    decide

end CommitGolfCandidate
