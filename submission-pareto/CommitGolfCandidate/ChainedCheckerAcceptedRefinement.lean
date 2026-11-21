import CommitGolfCandidate.ChainedCheckerRecordObserver

/-! Typed lower openings composed with the delivered cap observer. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open RecordLeaf RecordTail SplitCodec CheckerCap CheckerCap.Visit
set_option maxRecDepth 8192

def RecordedLowerOpening.complete {oracle index entry middle root rows}
    (opening : RecordedLowerOpening oracle index entry middle rows)
    (cap : RecordedPath canonicalEncoding calls width rows ((LENGTH+index.val)/2^16) 16 8 middle root) :
    RecordedOpening canonicalEncoding calls width oracle index entry root rows :=
  ⟨opening.nonce,opening.first,opening.second,recorded_path_append opening.path cap⟩

theorem checker_record_group_div (input : CheckInput) (record : Nat) :
    (LENGTH+(checkerRecordInputIndex input record).val)/2^16=checkerRecordGroup input record := by
  change (16777216+(checkerRecordInputIndex input record).val)/65536=
    256+(checkerRecordInputIndex input record).val/65536
  omega

theorem cap_boundary_opening (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (rows : List PublicRow) (stored : StoredLowerOpenings oracle input input.positions.card state rows)
    (record : Nat) (present : record < input.positions.card) :
    Nonempty (RecordedOpening canonicalEncoding calls width oracle (checkerRecordInputIndex input record)
      (input.values (checkerRecordValueItem input record present))
      (capHeapNode (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)).1.1 1)
      (rows++(capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)).1.2)) := by
  obtain ⟨opening⟩ := stored record present present
  have member := processed_group_member input record input.positions.card present present
  rw [checker_processed_groups_all] at member
  have cap := cap_marked_eight_recorded_path oracle (checker_decoded_cap_ready decoded boundary)
    (checkerRecordGroup input record) member (checker_record_group_bounds input record)
  refine ⟨(opening.mono (fun _ found => List.mem_append.mpr (.inl found))).complete ?_⟩
  rw [checker_record_group_div]
  exact cap.mono (fun _ found => List.mem_append.mpr (.inr found))

theorem decoded_full_record_opening (oracle : Oracle) {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (accepted : (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.rejected=false)
    (record : Nat) (present : record < input.positions.card) :
    let records := recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState records.1.1.state)
    Nonempty (RecordedOpening canonicalEncoding calls width oracle (checkerRecordInputIndex input record)
      (input.values (checkerRecordValueItem input record present)) (capHeapNode cap.1.1 1) (records.1.2++cap.1.2)) := by
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty decoded) (by omega : input.positions.card ≤ input.positions.card)
    (record_prefix_observation_support oracle input input.positions.card 0 (checkerRecordEntryState before))
  have boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0
      (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.state := by
    simpa only [Nat.zero_add,Nat.sub_self] using (good.continuation accepted).2
  exact cap_boundary_opening oracle decoded boundary _ (decoded_record_openings oracle nonempty decoded accepted) record present

theorem checker_input_commitment (input : CheckInput) :
    readBuffer (Artifact.submission.initialState .check input) Artifact.submission.layout.commitment 32=input.commitment := by
  have decoded := read_serialized_slice (Artifact.submission.initialState .check input) input.commitment
    Artifact.submission.layout.commitment 0 32 (by
      intro j inside
      rw [initial_input_byte Artifact.submission .check input _ (by change 4294971392+j<2^64;omega)]
      have selected : Artifact.submission.layout.commitment≤Artifact.submission.layout.commitment+j ∧
          Artifact.submission.layout.commitment+j<Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8 := by
        change 4294971392≤4294971392+j ∧ 4294971392+j<4294971392+32
        omega
      simp only [inputByte,Submission.inputBuffers,List.find?_cons,fixedBuffer,selected,and_self,
        decide_true,Nat.add_sub_cancel_left,Nat.zero_add])
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem checker_boundary_commitment {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state) :
    readBuffer state (8*536871424) 32=input.commitment := by
  have reference (word : Nat) (inside : word<4) :
      memoryView (checkerCryptoRecordState before) (536871424+word)=
        memoryView (Artifact.submission.initialState .check input) (536871424+word) := by
    apply TwoPermutationPrototype.Packed.Checker.word_eq_of_byte_frame
    intro offset small
    exact checker_crypto_record_public input footer before decoded (8*(536871424+word)+offset)
      (by omega) (by unfold checkingRawBase;omega)
  have frame : readBuffer state (8*536871424) 32=
      readBuffer (Artifact.submission.initialState .check input) (8*536871424) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro word inside
    have unchanged := (boundary.unread (536871424+word) (by omega) (by omega) (.inl (by omega))).trans (reference word inside)
    simpa only [memoryView,wordAddress,Nat.mul_add] using unchanged
  exact frame.trans (checker_input_commitment input)

theorem cap_boundary_commitment (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) :
    readBuffer (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1 (8*536871424) 32=input.commitment := by
  have reached : (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1∈support (capDfsEntryTrace
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)) := by
    rw [capDfsObservation]
    exact recorded_evaluation_support oracle _
  have post := cap_entry_post (cap_mark_ready (checker_decoded_cap_ready decoded boundary)) reached
  have frame : readBuffer (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1 (8*536871424) 32=readBuffer state (8*536871424) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro word inside
    have numeric : (wordAddress (536871424+word)).toNat=8*(536871424+word) := by
      simp only [wordAddress,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(536871424+word)<2^64)]
    have outside : OutsideCap (wordAddress (536871424+word)) := by
      refine ⟨⟨?_,?_,?_⟩,?_⟩
      · rw [numeric];omega
      · rw [numeric];omega
      · rw [numeric];omega
      · right;rw [numeric];omega
    have unchanged := (post.2.2.1 _ outside).trans (cap_marked_memory_word state boundary.marks
      (536871424+word) (by omega) (by omega))
    simpa only [memoryView,wordAddress,Nat.mul_add] using unchanged
  exact frame.trans (checker_boundary_commitment decoded boundary)

theorem cap_boundary_root_node (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state)
    (same : TwoPermutationPrototype.Checker.capRootAt
      (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)).1.1 1=
      readBuffer (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
        (capMarkedState state)).1.1 (8*536871424) 32) :
    capHeapNode (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1 1=input.commitment.extractLsb' 0 238 := by
  rw [capHeapNode]
  change (TwoPermutationPrototype.Checker.capRootAt _ 1).setWidth 238=_
  rw [same,cap_boundary_commitment oracle decoded boundary]
  exact BitVec.setWidth_eq_extractLsb' (by decide)

theorem checker_record_item_covers (input : CheckInput) (index : {i // i∈input.positions}) :
    ∃ record, ∃ present : record < input.positions.card, checkerRecordValueItem input record present=index := by
  have member : index∈input.positions.attach.sort (fun i j => i.val≤j.val) := by
    rw [Finset.mem_sort]
    exact Finset.mem_attach _ _
  obtain ⟨record,present,same⟩ := List.mem_iff_getElem.mp member
  refine ⟨record,by simpa using present,?_⟩
  exact same

theorem decoded_index_opening (oracle : Oracle) {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (accepted : (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.rejected=false)
    (index : {i // i∈input.positions}) :
    let records := recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState records.1.1.state)
    Nonempty (RecordedOpening canonicalEncoding calls width oracle index.val (input.values index)
      (capHeapNode cap.1.1 1) (records.1.2++cap.1.2)) := by
  obtain ⟨record,present,same⟩ := checker_record_item_covers input index
  have opening := decoded_full_record_opening oracle nonempty decoded accepted record present
  have indexed : checkerRecordInputIndex input record=index.val :=
    (checker_record_value_index input record present).symm.trans (congrArg Subtype.val same)
  dsimp only at opening ⊢
  rw [indexed,same] at opening
  exact opening

theorem cap_observed_root_execution (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) (fuel : Nat) :
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)
    ∃ finished : Execution,
      execute (Artifact.submission.image .check) (16+fuel) cap.1.1 false=pure finished ∧
      (finished.exit=.success → capHeapNode cap.1.1 1=input.commitment.extractLsb' 0 238) := by
  have reached : (capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup)
      (capMarkedState state)).1.1∈support (capDfsEntryTrace
        ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)) := by
    rw [capDfsObservation]
    exact recorded_evaluation_support oracle _
  have post := checker_decoded_cap_post decoded boundary reached
  obtain ⟨finished,success,calls,done,cycles,run⟩ := execute_root_check _ 536871424 fuel
    post.1 post.2.2.1 post.2.2.2 (by decide)
  refine ⟨finished,?_,?_⟩
  · rw [checking_manifest_image]
    exact run
  · intro accepted
    exact cap_boundary_root_node oracle decoded boundary (success.mp accepted).2

@[irreducible] noncomputable def capFinishObservation (oracle : Oracle) (input : CheckInput) (state : MachineState) (fuel : Nat) :=
  checkEvaluation oracle (recordRows (checkerCapFinish input state fuel))

theorem cap_finish_observation (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 state) (fuel : Nat) :
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)
    ∃ finished : Execution, capFinishObservation oracle input state fuel=((finished,cap.1.2),cap.2) ∧
      (finished.exit=.success → capHeapNode cap.1.1 1=input.commitment.extractLsb' 0 238) := by
  obtain ⟨finished,run,root⟩ := cap_observed_root_execution oracle decoded boundary fuel
  refine ⟨finished.charge
    (2556+capTreeSteps ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8+
      7*TwoPermutationPrototype.Checker.capHashCount ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8)
    (TwoPermutationPrototype.Checker.capHashCount ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8),?_,root⟩
  rw [capFinishObservation,checkerCapFinish,recorded_bind_evaluation]
  have observed : checkEvaluation oracle (recordRows (capDfsEntryTrace
      ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state)))=
      capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState state) := by
    rw [capDfsObservation]
  rw [observed]
  dsimp only
  simp only [run,pure_bind,record_rows_pure,check_evaluation_pure,List.append_nil,Nat.add_zero]

theorem observed_execution_charge (oracle : Oracle) (program : OracleComp World Execution) (cycles calls : Nat) :
    checkEvaluation oracle (recordRows (do let result ← program; return result.charge cycles calls))=
      let observed := checkEvaluation oracle (recordRows program)
      ((observed.1.1.charge cycles calls,observed.1.2),observed.2) := by
  simpa only [map_eq_bind_pure_comp,Function.comp_def] using
    record_map_evaluation oracle (fun result : Execution => result.charge cycles calls) program

@[irreducible] def checkerDecodedTail (input : CheckInput) (records : CheckerRecordPrefixResult) (fuel : Nat) : OracleComp World Execution := do
  let left := 3725*input.positions.card-records.instructions
  let groups := (input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup
  let capInstructions := 2556+capTreeSteps groups 1 8
  let result ← if records.rejected then
      execute (Artifact.submission.image .check) (left+61262+fuel) records.state false
    else checkerCapFinish input records.state (left+(61246-capInstructions)+fuel)
  return result.charge (2073+records.cycles) records.calls

theorem checker_decoded_run_tail (input : CheckInput) (before : MachineState) (fuel : Nat) :
    checkerDecodedRun input before fuel=checkerRecordPrefix input input.positions.card 0 (checkerRecordEntryState before) >>=
      fun records => checkerDecodedTail input records fuel := by
  unfold checkerDecodedRun checkerDecodedTail
  rfl

@[irreducible] noncomputable def decodedTailObservation (oracle : Oracle) (input : CheckInput)
    (records : CheckerRecordPrefixResult) (fuel : Nat) :=
  checkEvaluation oracle (recordRows (checkerDecodedTail input records fuel))

theorem decoded_tail_rejects (oracle : Oracle) (input : CheckInput) (records : CheckerRecordPrefixResult)
    (fuel : Nat) (flag : records.rejected=true) (pc : records.state.pc=4096+4*2738) :
    (decodedTailObservation oracle input records fuel).1.1.exit=.failure := by
  let remaining := 3725*input.positions.card-records.instructions+61262+fuel
  have room : 3≤remaining := by dsimp only [remaining];omega
  have run : execute (Artifact.submission.image .check) remaining records.state false=
      pure ⟨.failure,rejectState records.state,3,0⟩ := by
    rw [checking_manifest_image,show remaining=3+(remaining-3) by omega,execute_reject records.state pc]
  dsimp only [remaining] at run
  rw [decodedTailObservation,checkerDecodedTail]
  dsimp only
  simp only [flag,ite_true,run,pure_bind,record_rows_pure,check_evaluation_pure]
  rfl

theorem decoded_tail_accepts (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (records : CheckerRecordPrefixResult)
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 records.state)
    (flag : records.rejected=false) (fuel : Nat) :
    let cap := capDfsObservation oracle ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) (capMarkedState records.state)
    ∃ finished : Execution, decodedTailObservation oracle input records fuel=((finished,cap.1.2),cap.2) ∧
      (finished.exit=.success → capHeapNode cap.1.1 1=input.commitment.extractLsb' 0 238) := by
  let extra := 3725*input.positions.card-records.instructions+
    (61246-(2556+capTreeSteps ((input.positions.sort (·≤·)).map TwoPermutationPrototype.Sampling.capGroup) 1 8))+fuel
  obtain ⟨finished,equal,root⟩ := cap_finish_observation oracle decoded boundary extra
  refine ⟨finished.charge (2073+records.cycles) records.calls,?_,root⟩
  rw [decodedTailObservation,checkerDecodedTail]
  dsimp only
  simp only [flag,Bool.false_eq_true,ite_false,observed_execution_charge]
  rw [capFinishObservation] at equal
  rw [equal]

@[irreducible] noncomputable def decodedObservation (oracle : Oracle) (input : CheckInput) (before : MachineState) (fuel : Nat) :=
  checkEvaluation oracle (recordRows (checkerDecodedRun input before fuel))

theorem decoded_observation_step (oracle : Oracle) (input : CheckInput) (before : MachineState) (fuel : Nat) :
    decodedObservation oracle input before fuel=
      let records := recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)
      let later := decodedTailObservation oracle input records.1.1 fuel
      ((later.1.1,records.1.2++later.1.2),records.2+later.2) := by
  rw [decodedObservation,checker_decoded_run_tail,recorded_bind_evaluation,←record_prefix_observation_eq]
  simp only [decodedTailObservation]

theorem decoded_observation_openings (oracle : Oracle) {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (fuel : Nat)
    (accepted : (decodedObservation oracle input before fuel).1.1.exit=.success) :
    ∀ index : {i // i∈input.positions}, Nonempty (RecordedOpening canonicalEncoding calls width oracle index.val
      (input.values index) (input.commitment.extractLsb' 0 238) (decodedObservation oracle input before fuel).1.2) := by
  intro index
  rw [decoded_observation_step] at accepted ⊢
  dsimp only at accepted ⊢
  generalize observed : recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)=records at accepted ⊢
  have good := checker_record_prefix_good (checker_record_boundary_initial nonempty decoded) (by omega : input.positions.card ≤ input.positions.card)
    (record_prefix_observation_support oracle input input.positions.card 0 (checkerRecordEntryState before))
  rw [observed] at good
  cases flag : records.1.1.rejected with
  | true =>
    have failure := decoded_tail_rejects oracle input records.1.1 fuel flag (good.badpc flag)
    rw [failure] at accepted
    contradiction
  | false =>
    have boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) input.positions.card 0 records.1.1.state := by
      simpa only [Nat.zero_add,Nat.sub_self] using (good.continuation flag).2
    obtain ⟨finished,equal,root⟩ := decoded_tail_accepts oracle decoded records.1.1 boundary flag fuel
    rw [equal] at accepted ⊢
    have earlier : (recordPrefixObservation oracle input input.positions.card 0 (checkerRecordEntryState before)).1.1.rejected=false := by
      rw [observed]
      exact flag
    have opening := decoded_index_opening oracle nonempty decoded earlier index
    dsimp only at opening
    rw [observed,root accepted] at opening
    exact opening

def ProgramObservationOpens (oracle : Oracle) (input : CheckInput) (program : OracleComp World Execution) : Prop :=
  let observed := checkEvaluation oracle (recordRows program)
  observed.1.1.exit=.success → ∀ index : {i // i∈input.positions},
    Nonempty (RecordedOpening canonicalEncoding calls width oracle index.val (input.values index)
      (input.commitment.extractLsb' 0 238) observed.1.2)

theorem program_opens_failure (oracle : Oracle) (input : CheckInput) (state : MachineState) (cycles calls : Nat) :
    ProgramObservationOpens oracle input (pure ⟨.failure,state,cycles,calls⟩) := by
  intro accepted
  simp only [record_rows_pure,check_evaluation_pure] at accepted
  contradiction

theorem program_opens_empty (oracle : Oracle) (input : CheckInput) (empty : input.positions.card=0)
    (program : OracleComp World Execution) : ProgramObservationOpens oracle input program := by
  intro accepted index
  have positive := Finset.card_pos.mpr (show input.positions.Nonempty from ⟨index.val,index.property⟩)
  omega

theorem program_opens_charge (oracle : Oracle) (input : CheckInput) (program : OracleComp World Execution)
    (cycles calls : Nat) (opens : ProgramObservationOpens oracle input program) :
    ProgramObservationOpens oracle input (do let result ← program; return result.charge cycles calls) := by
  dsimp only [ProgramObservationOpens] at opens ⊢
  rw [observed_execution_charge]
  exact opens

theorem program_opens_decoded (oracle : Oracle) {input : CheckInput} (nonempty : input.positions.card≠0)
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before : MachineState}
    (decoded : CheckerDecodedInput input footer before) (fuel : Nat) :
    ProgramObservationOpens oracle input (checkerDecodedRun input before fuel) := by
  dsimp only [ProgramObservationOpens]
  have observed : decodedObservation oracle input before fuel=checkEvaluation oracle (recordRows (checkerDecodedRun input before fuel)) := by
    rw [decodedObservation]
  rw [←observed]
  exact decoded_observation_openings oracle nonempty decoded fuel

theorem program_opens_rejected_block (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (cycles fuel : Nat) (room : cycles≤fuel) (bad : CheckerRejectedBlock state cycles) :
    ProgramObservationOpens oracle input (execute (Artifact.submission.image .check) fuel state false) := by
  obtain ⟨after,rejects⟩ := bad
  rw [show fuel=cycles+(fuel-cycles) by omega,rejects]
  exact program_opens_failure oracle input after cycles 0

theorem initial_admitted_program_opens (oracle : Oracle) (input : CheckInput) (nonempty : input.positions.card≠0)
    (lower : 482*input.positions.card ≤ input.proof.length) (upper : input.proof.length≤482*input.positions.card+3776)
    (fuel : Nat) (room : 110987+6112*input.positions.card≤fuel) :
    ProgramObservationOpens oracle input (execute (Artifact.submission.image .check) fuel
      (Artifact.submission.initialState .check input) false) := by
  rcases checker_decoded_input_cases input nonempty lower upper with rejected | admitted
  · obtain ⟨cycles,bound,bad⟩ := rejected
    exact program_opens_rejected_block oracle input _ cycles fuel (by omega) bad
  · obtain ⟨footer,before,cycles,bound,ran,decoded⟩ := admitted
    let extra := fuel-cycles-(2073+3725*input.positions.card+61262)
    rw [show fuel=cycles+(2073+3725*input.positions.card+61262+extra) by dsimp only [extra];omega,
      ran,checker_decoded_execution nonempty decoded extra]
    exact program_opens_charge oracle input _ cycles 0 (program_opens_decoded oracle nonempty decoded extra)

theorem initial_program_opens (oracle : Oracle) (input : CheckInput)
    (valid : input.proof.length≤Artifact.submission.sizes.proof) (fuel : Nat)
    (room : 110987+6112*input.positions.card≤fuel) :
    ProgramObservationOpens oracle input (execute (Artifact.submission.image .check) fuel
      (Artifact.submission.initialState .check input) false) := by
  by_cases empty : input.positions.card=0
  · exact program_opens_empty oracle input empty _
  let state := Artifact.submission.initialState .check input
  have regs := checker_input_registers input
  have cardinal : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  have maximum : 482*LENGTH+3776<2^64 := by decide +kernel
  have lengthBound : input.proof.length≤8355061248 := valid
  have lengthFit : input.proof.length<2^64 := by omega
  have lowFit : 482*input.positions.card<2^64 := by omega
  have highFit : 482*input.positions.card+3776<2^64 := by omega
  have minimum : checkerMinimumWord state=BitVec.ofNat 64 (482*input.positions.card) :=
    checker_minimum_of_count state _ cardinal regs.2.2.2.2.2.1
  have maximumWord : checkerMinimumWord state+1888+1888=BitVec.ofNat 64 (482*input.positions.card+3776) := by
    rw [minimum]
    change BitVec.ofNat 64 (482*input.positions.card)+BitVec.ofNat 64 1888+BitVec.ofNat 64 1888=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  have lowIff : BitVec.ult (state.getReg .x17) (checkerMinimumWord state) ↔ input.proof.length<482*input.positions.card := by
    rw [regs.2.2.2.2.2.2,minimum]
    simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthFit,Nat.mod_eq_of_lt lowFit]
  have highIff : BitVec.ult (checkerMinimumWord state+1888+1888) (state.getReg .x17) ↔
      482*input.positions.card+3776 < input.proof.length := by
    rw [regs.2.2.2.2.2.2,maximumWord]
    simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthFit,Nat.mod_eq_of_lt highFit]
  by_cases lower : 482*input.positions.card ≤ input.proof.length
  · have goodLow : ¬BitVec.ult (state.getReg .x17) (checkerMinimumWord state) := by rw [lowIff];omega
    by_cases upper : input.proof.length≤482*input.positions.card+3776
    · exact initial_admitted_program_opens oracle input empty lower upper fuel room
    · exact program_opens_rejected_block oracle input state 13 fuel (by omega)
        (checker_header_upper_rejects state regs.1 goodLow (highIff.mpr (by omega)))
  · exact program_opens_rejected_block oracle input state 10 fuel (by omega)
      (checker_header_lower_rejects state regs.1 (lowIff.mpr (by omega)))

theorem checker_run_program_opens (oracle : Oracle) (input : CheckInput) :
    ProgramObservationOpens oracle input (Artifact.submission.run .check input) := by
  by_cases valid : input.proof.length≤Artifact.submission.sizes.proof
  · have run : Artifact.submission.run .check input=execute (Artifact.submission.image .check)
        (Artifact.submission.steps .check) (Artifact.submission.initialState .check input) false := by
      simp [Submission.run,valid]
    rw [run]
    exact initial_program_opens oracle input valid _ (checker_initial_budgets input).1
  · have run : Artifact.submission.run .check input=pure ⟨.failure,initialMachine,0,0⟩ := by
      simp [Submission.run,valid]
    rw [run]
    exact program_opens_failure oracle input initialMachine 0 0

theorem checker_observation_adaptive_budget (oracle : Oracle) (input : CheckInput) :
    (TwoPermutationPrototype.Checker.checkObservation Artifact.submission oracle input).2≤CHECK_BUDGET input.positions.card := by
  rw [←checker_observation_accounting Artifact.submission oracle input]
  apply checker_run_query_budget input
  have reached := check_evaluation_support oracle (Artifact.submission.run .check input)
  have erase := congrArg Prod.fst (TwoPermutationPrototype.Checker.check_record_erase oracle (Artifact.submission.run .check input))
  rw [←erase] at reached
  exact reached

theorem checker_accepted_trace_refines : CommitGolfCandidate.Chained.Checker.AcceptedTraceRefines
    canonicalEncoding Artifact.submission := by
  intro oracle input
  dsimp only
  intro accepted
  have cardinal : input.positions.card≤16777216 := by
    have bounded : input.positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact bounded
  have limit : CHECK_BUDGET input.positions.card≤2^31 := by
    change 100*input.positions.card≤2147483648
    omega
  exact ⟨(checker_observation_adaptive_budget oracle input).trans limit,checker_run_program_opens oracle input accepted⟩

theorem delivered_checker_binding : Artifact.submission.scheme.Binding :=
  CommitGolfCandidate.Chained.Checker.binding_of_accepted_trace canonicalEncoding Artifact.submission checker_accepted_trace_refines

end CommitGolfCandidate.Chained.Native.Refinement
