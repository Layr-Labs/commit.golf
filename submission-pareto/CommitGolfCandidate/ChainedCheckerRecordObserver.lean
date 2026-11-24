import CommitGolfCandidate.ChainedCheckerRecordRefinement

/-! Preservation of every pinned leaf and lower witness in the delivered record observer. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open RecordLeaf RecordTail SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] groupRun

def StoredLowerOpenings (oracle : Oracle) (input : CheckInput) (count : Nat)
    (state : MachineState) (rows : List PublicRow) : Prop :=
  ∀ record, record<count → ∀ present : record < input.positions.card,
    Nonempty (RecordedLowerOpening oracle (checkerRecordInputIndex input record)
      (input.values (checkerRecordValueItem input record present))
      (capHeapNode state (checkerRecordGroup input record)) rows)

theorem processed_group_member (input : CheckInput) (record count : Nat)
    (earlier : record<count) (present : record < input.positions.card) :
    checkerRecordGroup input record∈checkerProcessedGroups input count := by
  have bound : record<(input.positions.sort (·≤·)).length := by simpa using present
  apply List.mem_take_iff_getElem.mpr
  refine ⟨record,by simpa only [List.length_map,Finset.length_sort] using Nat.lt_min.mpr ⟨earlier,present⟩,?_⟩
  simp only [List.getElem_map,checker_record_group_cap,checkerRecordInputIndex,List.getElem?_eq_getElem bound,Option.getD_some]

theorem record_step_stored (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record (remaining+1) state)
    (rows : List PublicRow) (stored : StoredLowerOpenings oracle input record state rows)
    (accepted : TwoPermutationPrototype.Checker.GroupAccepted
      (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)) :
    StoredLowerOpenings oracle input (record+1)
      (groupRun (recordLowerObservation oracle input record (754975239+32*record) state).1.1
        (checkerRecordGroup input record)).1
      (rows++(recordLowerObservation oracle input record (754975239+32*record) state).1.2) := by
  have reached := recorded_evaluation_support oracle (checkerRecordLowerTrace input record (754975239+32*record) state)
  rw [←record_lower_observation_eq] at reached
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary (by omega)
  intro earlier bounded present
  by_cases old : earlier<record
  · have preserved := record_group_prior_heap boundary reached (checkerRecordGroup input earlier)
      (checker_record_group_bounds input earlier) (processed_group_member input earlier record old present)
    rw [preserved]
    exact (stored earlier old present).map (fun opening => opening.mono (fun _ found => List.mem_append.mpr (.inl found)))
  · have same : earlier=record := by omega
    subst earlier
    have cardinal : input.positions.card≤16777216 := boundary.limit
    have small : remaining<2^64 := by have := boundary.balance;omega
    have ready := checker_record_group_ready core reached remaining boundary.counter small boundary.roots boundary.marks
    rw [group_run_heap_node ready accepted]
    exact ⟨(record_lower_opening oracle decoded boundary (by omega)).mono
      (fun _ found => List.mem_append.mpr (.inr found))⟩

@[irreducible] noncomputable def recordPrefixObservation (oracle : Oracle) (input : CheckInput)
    (count record : Nat) (state : MachineState) :=
  checkEvaluation oracle (recordRows (checkerRecordPrefix input count record state))

theorem record_prefix_observation_eq (oracle : Oracle) (input : CheckInput) (count record : Nat) (state : MachineState) :
    recordPrefixObservation oracle input count record state=
      checkEvaluation oracle (recordRows (checkerRecordPrefix input count record state)) := by rw [recordPrefixObservation]

theorem record_prefix_observation_support (oracle : Oracle) (input : CheckInput) (count record : Nat) (state : MachineState) :
    (recordPrefixObservation oracle input count record state).1.1∈support (checkerRecordPrefix input count record state) := by
  rw [record_prefix_observation_eq]
  exact recorded_evaluation_support oracle _

theorem record_prefix_observation_zero (oracle : Oracle) (input : CheckInput) (record : Nat) (state : MachineState) :
    recordPrefixObservation oracle input 0 record state=((CheckerRecordPrefixResult.stopped state false,[]),0) := by
  rw [record_prefix_observation_eq,checkerRecordPrefix,record_rows_pure,check_evaluation_pure]

theorem record_prefix_observation_step (oracle : Oracle) (input : CheckInput) (count record : Nat) (state : MachineState) :
    recordPrefixObservation oracle input (count+1) record state=
      let first := recordLowerObservation oracle input record (754975239+32*record) state
      let tail := groupRun first.1.1 (checkerRecordGroup input record)
      let instructions := checkerFirstOrderingInput input record+3656+tail.2
      let cycles := checkerFirstOrderingInput input record+4300+tail.2
      if TwoPermutationPrototype.Checker.GroupAccepted first.1.1 (checkerRecordGroup input record) then
        let later := recordPrefixObservation oracle input count (record+1) tail.1
        ((later.1.1.addRecord instructions cycles,first.1.2++later.1.2),first.2+later.2)
      else (((CheckerRecordPrefixResult.stopped tail.1 true).addRecord instructions cycles,first.1.2),first.2) := by
  rw [record_prefix_observation_eq,checkerRecordPrefix,recorded_bind_evaluation,←record_lower_observation_eq]
  dsimp only
  split
  · have mapped := record_map_evaluation oracle
      (fun result : CheckerRecordPrefixResult => result.addRecord
        (checkerFirstOrderingInput input record+3656+(groupRun
          (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)).2)
        (checkerFirstOrderingInput input record+4300+(groupRun
          (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)).2))
      (checkerRecordPrefix input count (record+1) (groupRun
        (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)).1)
    rw [map_eq_bind_pure_comp,Function.comp_def] at mapped
    rw [mapped,←record_prefix_observation_eq]
  · rw [record_rows_pure,check_evaluation_pure]
    simp only [List.append_nil,Nat.add_zero]

theorem record_observer_induction {α : Type}
    (observe : Nat → Nat → α → (α × Bool) × List PublicRow)
    (advance : Nat → α → α) (stepRows : Nat → α → List PublicRow) (okay : Nat → α → Bool)
    (ready : Nat → Nat → α → Prop) (invariant : Nat → α → List PublicRow → Prop)
    (zero : ∀ record state, observe 0 record state=((state,false),[]))
    (step : ∀ count record state, observe (count+1) record state=
      if okay record state then
        let later := observe count (record+1) (advance record state)
        ((later.1.1,later.1.2),stepRows record state++later.2)
      else ((advance record state,true),stepRows record state))
    (nextReady : ∀ count record state, ready (count+1) record state → okay record state=true →
      ready count (record+1) (advance record state))
    (nextStored : ∀ count record state rows, ready (count+1) record state → invariant record state rows → okay record state=true →
      invariant (record+1) (advance record state) (rows++stepRows record state)) (count : Nat) :
    ∀ record state rows, ready count record state → invariant record state rows →
      (observe count record state).1.2=false →
      invariant (record+count) (observe count record state).1.1 (rows++(observe count record state).2) := by
  induction count with
  | zero =>
    intro record state rows prepared stored accepted
    rw [zero]
    simpa only [Nat.add_zero,List.append_nil] using stored
  | succ count ih =>
    intro record state rows prepared stored accepted
    rw [step] at accepted ⊢
    by_cases good : okay record state=true
    · simp only [good,ite_true] at accepted ⊢
      have rest := ih (record+1) (advance record state) (rows++stepRows record state)
        (nextReady count record state prepared good) (nextStored count record state rows prepared stored good) accepted
      rw [show record+1+count=record+(count+1) by omega] at rest
      simpa only [List.append_assoc] using rest
    · simp only [good,Bool.false_eq_true,ite_false,Bool.true_eq_false] at accepted

@[irreducible] def recordResultProjection (observed : (CheckerRecordPrefixResult × List PublicRow) × Nat) :
    (MachineState × Bool) × List PublicRow :=
  ((observed.1.1.state,observed.1.1.rejected),observed.1.2)

theorem record_result_projection_add (later : (CheckerRecordPrefixResult × List PublicRow) × Nat)
    (earlier : List PublicRow) (instructions cycles calls : Nat) :
    recordResultProjection ((later.1.1.addRecord instructions cycles,earlier++later.1.2),calls)=
      (((recordResultProjection later).1.1,(recordResultProjection later).1.2),earlier++(recordResultProjection later).2) := by
  simp only [recordResultProjection,CheckerRecordPrefixResult.addRecord]

theorem record_result_projection_stopped (state : MachineState) (flag : Bool) (rows : List PublicRow) (calls : Nat) :
    recordResultProjection ((CheckerRecordPrefixResult.stopped state flag,rows),calls)=((state,flag),rows) := by
  rw [recordResultProjection]
  rfl

theorem record_result_projection_stopped_add (state : MachineState) (flag : Bool) (rows : List PublicRow)
    (calls instructions cycles : Nat) :
    recordResultProjection (((CheckerRecordPrefixResult.stopped state flag).addRecord instructions cycles,rows),calls)=
      ((state,flag),rows) := by
  simp only [recordResultProjection,CheckerRecordPrefixResult.addRecord,CheckerRecordPrefixResult.stopped]

@[irreducible] noncomputable def recordPrefixView (oracle : Oracle) (input : CheckInput)
    (count record : Nat) (state : MachineState) : (MachineState × Bool) × List PublicRow :=
  recordResultProjection (recordPrefixObservation oracle input count record state)

theorem record_prefix_view_zero (oracle : Oracle) (input : CheckInput) (record : Nat) (state : MachineState) :
    recordPrefixView oracle input 0 record state=((state,false),[]) := by
  rw [recordPrefixView,record_prefix_observation_zero]
  exact record_result_projection_stopped state false [] 0

theorem record_prefix_view_step (oracle : Oracle) (input : CheckInput) (count record : Nat) (state : MachineState) :
    recordPrefixView oracle input (count+1) record state=
      let first := recordLowerObservation oracle input record (754975239+32*record) state
      let next := (groupRun first.1.1 (checkerRecordGroup input record)).1
      if decide (TwoPermutationPrototype.Checker.GroupAccepted first.1.1 (checkerRecordGroup input record)) then
        let later := recordPrefixView oracle input count (record+1) next
        ((later.1.1,later.1.2),first.1.2++later.2)
      else ((next,true),first.1.2) := by
  by_cases good : TwoPermutationPrototype.Checker.GroupAccepted
    (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)
  all_goals simp only [recordPrefixView,record_prefix_observation_step,good,ite_true,ite_false,
    decide_true,decide_false,Bool.false_eq_true,record_result_projection_add,record_result_projection_stopped_add]

theorem record_prefix_stored (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (count : Nat) :
    ∀ (record remaining : Nat) (state : MachineState),
    CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state → count≤remaining →
    ∀ rows, StoredLowerOpenings oracle input record state rows →
    (recordPrefixObservation oracle input count record state).1.1.rejected=false →
    StoredLowerOpenings oracle input (record+count)
      (recordPrefixObservation oracle input count record state).1.1.state
      (rows++(recordPrefixObservation oracle input count record state).1.2) := by
  intro record remaining state boundary enough rows stored accepted
  have result := record_observer_induction (recordPrefixView oracle input)
    (fun record state => (groupRun (recordLowerObservation oracle input record (754975239+32*record) state).1.1
      (checkerRecordGroup input record)).1)
    (fun record state => (recordLowerObservation oracle input record (754975239+32*record) state).1.2)
    (fun record state => decide (TwoPermutationPrototype.Checker.GroupAccepted
      (recordLowerObservation oracle input record (754975239+32*record) state).1.1 (checkerRecordGroup input record)))
    (fun count record state => ∃ remaining, CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state ∧ count≤remaining)
    (StoredLowerOpenings oracle input) (record_prefix_view_zero oracle input) (record_prefix_view_step oracle input)
    (by
      intro count record state prepared good
      obtain ⟨remaining,boundary,enough⟩ := prepared
      cases remaining with
      | zero => omega
      | succ remaining =>
        have reached := recorded_evaluation_support oracle (checkerRecordLowerTrace input record (754975239+32*record) state)
        rw [←record_lower_observation_eq] at reached
        exact ⟨remaining,checker_record_boundary_next boundary reached (of_decide_eq_true good),by omega⟩)
    (by
      intro count record state rows prepared stored good
      obtain ⟨remaining,boundary,enough⟩ := prepared
      cases remaining with
      | zero => omega
      | succ remaining => exact record_step_stored oracle decoded boundary rows stored (of_decide_eq_true good))
    count record state rows ⟨remaining,boundary,enough⟩ stored
  have acceptedView : (recordPrefixView oracle input count record state).1.2=false := by
    rw [recordPrefixView,recordResultProjection]
    exact accepted
  simpa only [recordPrefixView,recordResultProjection] using result acceptedView

theorem decoded_record_openings (oracle : Oracle) {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (accepted : (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.rejected=false) :
    StoredLowerOpenings oracle input input.positions.card
      (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.state
      (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.2 := by
  have stored : StoredLowerOpenings oracle input 0 (checkerRecordEntryState before) [] := by
    intro record earlier present
    omega
  simpa only [Nat.zero_add,List.nil_append] using record_prefix_stored oracle decoded input.positions.card
    0 input.positions.card (checkerRecordEntryState before) (checker_record_boundary_initial nonempty decoded)
    (by omega) [] stored accepted

end CommitGolfCandidate.Chained.Native.Refinement
