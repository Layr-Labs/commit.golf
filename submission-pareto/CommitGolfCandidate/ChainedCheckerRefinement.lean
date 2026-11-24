import CommitGolfCandidate.ChainedCheckerRecordFinish
import CommitGolfCandidate.ChainedCheckerLeafData
import CommitGolfCandidate.ChainedCheckerReplay

/-! Recorded observations of the delivered chained checker. -/
namespace CommitGolfCandidate.Chained.Native.Refinement
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_record_erase)
open RecordTail
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open RecordLeaf SplitCodec
open TwoPermutationPrototype.Packed.RecordLeaf (checkerNonce)

theorem checker_evaluation_counted (candidate : Submission) (oracle : Oracle) (input : CheckInput) :
    (checkEvaluation oracle (candidate.run .check input)).1.oracleCalls=
      (checkEvaluation oracle (candidate.run .check input)).2 := by
  by_cases valid : input.proof.length≤candidate.sizes.proof
  · have run : candidate.run .check input=execute (candidate.image .check) (candidate.steps .check)
        (candidate.initialState .check input) false := by
      simp [Submission.run,valid]
    have reached : checkEvaluation oracle (candidate.run .check input)∈support
        (oracle.run (execute (candidate.image .check) (candidate.steps .check)
          (candidate.initialState .check input) false)) := by
      rw [execute_check_evaluation,←run]
      simp only [support_pure,Set.mem_singleton_iff]
    exact execute_counted oracle _ _ _ _ reached
  · simp [Submission.run,valid,check_evaluation_pure]

theorem checker_observation_accounting (candidate : Submission) (oracle : Oracle) (input : CheckInput) :
    (checkObservation candidate oracle input).1.1.oracleCalls=(checkObservation candidate oracle input).2 := by
  have counted := checker_evaluation_counted candidate oracle input
  rw [←check_record_erase oracle (candidate.run .check input)] at counted
  exact counted

theorem checker_observation_resources (oracle : Oracle) (input : CheckInput) :
    let observed := checkObservation Artifact.submission oracle input
    observed.1.1.exit≠.unfinished ∧ observed.1.1.cycles≤Artifact.submission.steps .check ∧ observed.2≤2^31 := by
  have reached := check_evaluation_support oracle (Artifact.submission.run .check input)
  have erase := congrArg Prod.fst (check_record_erase oracle (Artifact.submission.run .check input))
  rw [←erase] at reached
  have limits := checker_run_limits input reached
  have budgets := checker_initial_budgets input
  refine ⟨limits.1,limits.2.1.trans budgets.2.1,?_⟩
  rw [←checker_observation_accounting Artifact.submission oracle input]
  exact limits.2.2.trans budgets.2.2

def checkerDecodedRecordAt (input : CheckInput) (record : Nat) : InteriorCodec.Record :=
  (checkerDecodeRecords input.positions.card input.proof)[record]?.getD (decode InteriorCodec.recordSpec [])

def checkerRecordValueItem (input : CheckInput) (record : Nat) (present : record < input.positions.card) :
    {index // index∈input.positions} :=
  (input.positions.attach.sort (fun i j => i.val≤j.val))[record]'(by simpa using present)

theorem checker_record_value_index (input : CheckInput) (record : Nat) (present : record < input.positions.card) :
    (checkerRecordValueItem input record present).val=checkerRecordInputIndex input record := by
  have small : record<(input.positions.sort (·≤·)).length := by simpa using present
  simpa only [checkerRecordValueItem,checkerRecordInputIndex,List.getElem?_eq_getElem small,Option.getD_some] using
    checker_loaded_value_index input record present

private theorem raw_record_bytes_at (state : MachineState) (records : List InteriorCodec.Record) (footer : Proof)
    (pointer : Nat) (memory : BytesAt state (BitVec.ofNat 64 pointer) (rawRecordStream records++footer))
    (record : Nat) (present : record<records.length) :
    BytesAt state (BitVec.ofNat 64 (pointer+498*record)) (rawFieldsBytes (recordRawFields records[record])) := by
  induction records generalizing pointer record with
  | nil => simp at present
  | cons head tail ih =>
    change BytesAt state _ ((rawFieldsBytes (recordRawFields head)++rawRecordStream tail)++footer) at memory
    rw [List.append_assoc,bytes_at_append,record_raw_fields_length,←BitVec.ofNat_add] at memory
    cases record with
    | zero => simpa using memory.1
    | succ record =>
      have remaining := ih (pointer+498) memory.2 record (by simpa using present)
      have address : pointer+498*(record+1)=(pointer+498)+498*record := by omega
      simpa only [address,List.getElem_cons_succ] using remaining

theorem checker_boundary_raw_memory {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    BytesAt state (BitVec.ofNat 64 (checkingRawBase+498*record))
      (rawFieldsBytes (recordRawFields (checkerDecodedRecordAt input record))) := by
  have present : record < input.positions.card := by have := boundary.balance;omega
  have small : record<(checkerDecodeRecords input.positions.card input.proof).length := by
    simpa only [checker_decode_records_length] using present
  have raw := raw_record_bytes_at (checkerCryptoRecordState before) _ _ checkingRawBase
    (checker_crypto_record_input_memory input footer before decoded) record small
  change BytesAt _ _ (rawFieldsBytes (recordRawFields
    ((checkerDecodeRecords input.positions.card input.proof)[record]?.getD (decode InteriorCodec.recordSpec []))))
  rw [List.getElem?_eq_getElem small,Option.getD_some]
  have large : 8*(754975239+32*LENGTH)≤checkingRawBase := by decide +kernel
  have low : 32768≤checkingRawBase := by decide +kernel
  have high : checkingRawBase+498*LENGTH+528≤2^36 := by decide +kernel
  intro index inside
  have length : index<498 := by simpa only [record_raw_fields_length] using inside
  rw [←BitVec.ofNat_add]
  have same := TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame (checkerCryptoRecordState before) state
    (checkingRawBase+498*record+index) (boundary.unread _ (by omega) (by have := boundary.limit;omega)
      (Or.inr (by have := boundary.balance;have := boundary.limit;omega)))
  exact same.trans (by simpa only [←BitVec.ofNat_add] using raw index inside)

theorem checker_record_value_data {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    readBuffer (checkerRecordCoreNonceState state) (6039801952+256*record) 256=
      input.values (checkerRecordValueItem input record (by have := boundary.balance;omega)) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  have present : record < input.positions.card := by have := boundary.balance;omega
  have high : 6039801952+256*LENGTH+256<checkingRawBase := by decide +kernel
  have room : 6039801952+256*LENGTH+256<2^36 := by decide +kernel
  rw [checker_record_core_nonce_buffer core _ _ (by omega) (by have := boundary.limit;omega)]
  have frame : readBuffer state (6039801952+256*record) 256=
      readBuffer (Artifact.submission.initialState .check input) (6039801952+256*record) 256 := by
    apply lower_buffer_bytes
    intro index inside
    have same := TwoPermutationPrototype.Packed.Checker.byte_eq_of_word_frame (checkerCryptoRecordState before) state
      (6039801952+256*record+index) (boundary.unread _ (by omega) (by have := boundary.limit;omega) (Or.inr (by omega)))
    exact same.trans (checker_crypto_record_public input footer before decoded _ (by omega) (by have := boundary.limit;omega))
  rw [frame]
  exact checker_loaded_value input record present

private theorem read_raw_record_nonce (state : MachineState) (pointer : Nat) (record : InteriorCodec.Record)
    (raw : BytesAt state (BitVec.ofNat 64 pointer) (rawFieldsBytes (recordRawFields record))) :
    readBuffer state pointer 16=checkerDecodedNonce record := by
  have bytes (index : Nat) (inside : index<16) :
      state.getByte (BitVec.ofNat 64 (pointer+index))=(checkerDecodedNonce record).extractLsb' (8*index) 8 := by
    have bound : index<(rawFieldsBytes (recordRawFields record)).length := by rw [record_raw_fields_length];omega
    have memory := raw index bound
    rw [←BitVec.ofNat_add] at memory
    rw [memory]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using
      checker_record_raw_nonce_byte record index inside
  have decoded := read_serialized_slice state (checkerDecodedNonce record) pointer 0 16 (by
    intro index inside
    simpa only [Nat.zero_add] using bytes index inside)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem checker_record_nonce_data {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    readBuffer (checkerRecordCoreNonceState state) 12272 16=checkerDecodedNonce (checkerDecodedRecordAt input record) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  have copy := checker_copy_buffer .nonce (checkerRecordHeadPrefix 6 state) (checkingRawBase+498*record) 12272
    (checker_record_core_nonce_ready core) (by
      have low : 32768≤checkingRawBase := by decide +kernel
      omega)
  have copied : readBuffer (checkerRecordCoreNonceState state) 12272 16=
      readBuffer (checkerRecordHeadPrefix 6 state) (checkingRawBase+498*record) 16 := by
    simpa only [checkerRecordCoreNonceState,CheckerCopySite.count,Nat.reduceMul] using copy
  have frame : readBuffer (checkerRecordHeadPrefix 6 state) (checkingRawBase+498*record) 16=
      readBuffer state (checkingRawBase+498*record) 16 := by
    apply read_buffer_memory_congr
    funext query
    exact checker_record_head_memory 6 state (by decide) query
  rw [copied,frame]
  exact read_raw_record_nonce _ _ _ (checker_boundary_raw_memory decoded boundary active)

private theorem buffer_window (state : MachineState) (start count : Nat) :
    window (memoryView state) start=
      (fun i : Fin count => (readBuffer state (8*start) (8*count)).extractLsb' (64*i.val) 64) := by
  funext i
  change memoryView state (start+i.val)=_
  rw [←TwoPermutationPrototype.Packed.Checker.read_buffer_word]
  have slice := read_buffer_slice state (8*start) (8*count) (8*i.val) 8 (by have := i.isLt;omega)
  simpa only [Nat.mul_add,←Nat.mul_assoc,Nat.reduceMul] using slice.symm

theorem checker_record_value_words {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    window (memoryView (checkerRecordCoreNonceState state)) (754975239+32*record+5)=
      (fun i : Fin 32 => (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega))).extractLsb'
        (64*i.val) 64) := by
  rw [buffer_window,show 8*(754975239+32*record+5)=6039801952+256*record by omega,
    checker_record_value_data decoded boundary active]
  rfl

theorem checker_record_nonce_words {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    checkerNonce (checkerRecordCoreNonceState state)=saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record)) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  rw [checker_nonce_words _ 1534 (checker_record_core_leaf_ready core).proofPointer,buffer_window]
  change (fun i : Fin 2 => (readBuffer (checkerRecordCoreNonceState state) 12272 16).extractLsb' (64*i.val) 64)=_
  rw [checker_record_nonce_data decoded boundary active]
  rfl

theorem checker_record_typed_leaf_rows (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    let source := 754975239+32*record
    let message : Words 32 := fun i =>
      (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega))).extractLsb' (64*i.val) 64
    let nonce := saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record))
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation (checkerRecordInputIndex input record) nonce a.2 message
    checkEvaluation oracle (recordRows (leafQueries (checkerRecordCoreNonceState state) source
      (checkerRecordInputIndex input record)))=
      ((secondReplyState (checkerRecordCoreNonceState state) source a.2 b.2,
        [.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  dsimp only
  rw [CommitGolfCandidate.Chained.Native.RecordLeaf.checker_leaf_rows,
    checker_record_value_words decoded boundary active,checker_record_nonce_words decoded boundary active]

theorem checker_record_typed_leaf_digest (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    let message : Words 32 := fun i =>
      (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega))).extractLsb' (64*i.val) 64
    let nonce := saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record))
    readBuffer (checkEvaluation oracle (recordRows (leafQueries (checkerRecordCoreNonceState state)
      (754975239+32*record) (checkerRecordInputIndex input record)))).1.1 12288 32=
      pinnedLeafDigest oracle.permutation (checkerRecordInputIndex input record) nonce message := by
  dsimp only
  rw [checker_record_typed_leaf_rows oracle decoded boundary active]
  exact checker_leaf_digest _ _ _ _

theorem checker_record_typed_leaf_path_digest (oracle : Oracle) {input : CheckInput}
    {footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))} {before state : MachineState}
    (decoded : CheckerDecodedInput input footer before) {record remaining : Nat}
    (boundary : CheckerRecordBoundary input (checkerCryptoRecordState before) record remaining state)
    (active : remaining≠0) :
    let message : Words 32 := fun i =>
      (input.values (checkerRecordValueItem input record (by have := boundary.balance;omega))).extractLsb' (64*i.val) 64
    let nonce := saltWords (checkerDecodedNonce (checkerDecodedRecordAt input record))
    readBuffer (checkerLeafPathState (checkEvaluation oracle (recordRows (leafQueries (checkerRecordCoreNonceState state)
      (754975239+32*record) (checkerRecordInputIndex input record)))).1.1) 12288 32=
      BitVec.ofNat 256 ((pinnedLeafDigest oracle.permutation (checkerRecordInputIndex input record) nonce message).toNat%2^238) := by
  obtain ⟨fit,core⟩ := checker_record_boundary_core boundary active
  dsimp only
  rw [checker_record_typed_leaf_rows oracle decoded boundary active]
  exact checker_leaf_path_digest (checker_record_core_leaf_ready core) _ _

noncomputable def canonicalChainValue (oracle : Oracle) (height : Height) (seed : Seed) : Nat → Output
  | 0 => oracle.compression (canonicalEncoding.first height seed)
  | stage+1 => oracle.compression (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))

noncomputable def canonicalContinuationRows (oracle : Oracle) (height : Height) (seed : Seed) :
    Nat → Nat → List PublicRow
  | _,0 => []
  | stage,count+1 => .compression (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))
      (canonicalChainValue oracle height seed (stage+1))::canonicalContinuationRows oracle height seed (stage+1) count

theorem canonical_continuation_recorded (oracle : Oracle) (height : Height) (seed : Seed) (stage count : Nat) :
    checkEvaluation oracle (recordRows (continuationTrace height stage count (canonicalChainValue oracle height seed stage)))=
      ((canonicalChainValue oracle height seed (stage+count),canonicalContinuationRows oracle height seed stage count),count) := by
  induction count generalizing stage with
  | zero => simp [continuationTrace,record_rows_pure,check_evaluation_pure,canonicalContinuationRows]
  | succ count ih =>
    have recorded : recordRows (continuationTrace height stage (count+1) (canonicalChainValue oracle height seed stage))=
        (do let answer ← (liftM (World.query (.inr (.inl
              (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))))) : OracleComp World Output)
            (fun result => (result.1,PublicRow.compression
              (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage)) answer::result.2)) <$>
              recordRows (continuationTrace height (stage+1) count answer)) := by
      exact record_rows_query (.inr (.inl (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))))
        (fun answer => continuationTrace height (stage+1) count answer)
    have first : checkEvaluation oracle (liftM (World.query (.inr (.inl
          (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))))) : OracleComp World Output)=
        (canonicalChainValue oracle height seed (stage+1),1) := by rfl
    rw [recorded,check_evaluation_bind,first]
    dsimp only
    rw [check_evaluation_map]
    change (((checkEvaluation oracle (recordRows (continuationTrace height (stage+1) count
      (canonicalChainValue oracle height seed (stage+1))))).1.1,
      .compression (encodeNext height (stage+1) (canonicalChainValue oracle height seed stage))
        (canonicalChainValue oracle height seed (stage+1))::
        (checkEvaluation oracle (recordRows (continuationTrace height (stage+1) count
          (canonicalChainValue oracle height seed (stage+1))))).1.2),
      1+(checkEvaluation oracle (recordRows (continuationTrace height (stage+1) count
        (canonicalChainValue oracle height seed (stage+1))))).2)=_
    rw [ih]
    simp only [canonicalContinuationRows,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem canonical_continuation_has_row (oracle : Oracle) (height : Height) (seed : Seed)
    (stage count index : Nat) (afterStage : stage < index) (present : index ≤ stage+count) :
    PublicRow.compression (encodeNext height index (canonicalChainValue oracle height seed (index-1)))
      (canonicalChainValue oracle height seed index)∈canonicalContinuationRows oracle height seed stage count := by
  induction count generalizing stage with
  | zero => omega
  | succ count ih =>
    rw [canonicalContinuationRows,List.mem_cons]
    by_cases first : index=stage+1
    · left
      subst index
      simp
    · right
      exact ih (stage+1) (by omega) (by omega)

noncomputable def canonicalQueries (height : Height) (seed : Seed) : OracleComp World Output := do
  let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first height seed)))) : OracleComp World Output)
  continuationTrace height 0 (calls height-1) answer

theorem canonical_queries_recorded (oracle : Oracle) (height : Height) (seed : Seed) :
    checkEvaluation oracle (recordRows (canonicalQueries height seed))=
      ((canonicalChainValue oracle height seed (calls height-1),
        .compression (canonicalEncoding.first height seed) (canonicalChainValue oracle height seed 0)::
          canonicalContinuationRows oracle height seed 0 (calls height-1)),calls height) := by
  have positive := calls_positive height
  have recorded : recordRows (canonicalQueries height seed)=
      (do let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first height seed)))) : OracleComp World Output)
          (fun result => (result.1,PublicRow.compression (canonicalEncoding.first height seed) answer::result.2)) <$>
            recordRows (continuationTrace height 0 (calls height-1) answer)) := by
    exact record_rows_query (.inr (.inl (canonicalEncoding.first height seed)))
      (fun answer => continuationTrace height 0 (calls height-1) answer)
  have first : checkEvaluation oracle
      (liftM (World.query (.inr (.inl (canonicalEncoding.first height seed)))) : OracleComp World Output)=
      (canonicalChainValue oracle height seed 0,1) := by rfl
  rw [recorded,check_evaluation_bind,first]
  dsimp only
  rw [check_evaluation_map]
  change (((checkEvaluation oracle (recordRows (continuationTrace height 0 (calls height-1)
    (canonicalChainValue oracle height seed 0)))).1.1,
    .compression (canonicalEncoding.first height seed) (canonicalChainValue oracle height seed 0)::
      (checkEvaluation oracle (recordRows (continuationTrace height 0 (calls height-1)
        (canonicalChainValue oracle height seed 0)))).1.2),
    1+(checkEvaluation oracle (recordRows (continuationTrace height 0 (calls height-1)
      (canonicalChainValue oracle height seed 0)))).2)=_
  rw [canonical_continuation_recorded]
  simp only [Nat.zero_add,Nat.add_sub_cancel' positive]

theorem canonical_queries_chain (oracle : Oracle) (height : Height) (seed : Seed) :
    RecordedChain canonicalEncoding calls (checkEvaluation oracle (recordRows (canonicalQueries height seed))).1.2
      height seed (canonicalChainValue oracle height seed) := by
  rw [canonical_queries_recorded]
  refine ⟨calls_positive height,calls_bound height,?_⟩
  intro index present
  cases index with
  | zero => simp [stageInput]
  | succ index =>
    apply List.mem_cons_of_mem
    simpa only [stageInput,Nat.add_one_ne_zero,ite_false,canonicalEncoding] using
      canonical_continuation_has_row oracle height seed 0 (calls height-1) (index+1) (by omega) (by omega)

theorem record_map_evaluation {α β : Type} (oracle : Oracle) (f : α → β) (program : OracleComp World α) :
    checkEvaluation oracle (recordRows (f <$> program))=
      ((f (checkEvaluation oracle (recordRows program)).1.1,(checkEvaluation oracle (recordRows program)).1.2),
        (checkEvaluation oracle (recordRows program)).2) := by
  have recorded : recordRows (f <$> program)=(fun result => (f result.1,result.2)) <$> recordRows program := by
    simp only [map_eq_bind_pure_comp,Function.comp_def,record_rows_bind,record_rows_pure,bind_assoc,pure_bind,List.append_nil]
  rw [recorded,check_evaluation_map]

theorem checker_hash_recorded_chain (oracle : Oracle) (site : CheckerHashSite) (remaining : Nat) (small : remaining≤7)
    (state : MachineState) (args : LoopArgs state 256) (height : Height) (left right : BitVec 238)
    (heightReg : state.getReg .x17=BitVec.ofNat 64 height.val) (mask : state.getReg .x16=finalMask height)
    (count : remaining+1=calls height)
    (inputs : ∀ word : Fin 8, state.getMem (state.getReg .x14+BitVec.ofNat 64 (8*word.val))=
      if word.val<4 then childWord left word.val else childWord right (word.val-4)) :
    let observed := checkEvaluation oracle (recordRows (checkerHashTrace site remaining state))
    RecordedChain canonicalEncoding calls observed.1.2 height (right++left)
      (canonicalChainValue oracle height (right++left)) ∧
      readBuffer observed.1.1 256 32=finalValue height
        (canonicalChainValue oracle height (right++left) (calls height-1)) := by
  have content := checker_hash_content site remaining small state args height left right heightReg mask inputs
  have remainingEq : remaining=calls height-1 := by omega
  have mapped : (fun out => readBuffer out 256 32) <$> checkerHashTrace site remaining state=
      finalValue height <$> canonicalQueries height (right++left) := by
    simpa only [map_eq_bind_pure_comp,Function.comp_def,canonicalQueries,bind_assoc,remainingEq] using content
  have same := congrArg (fun program => checkEvaluation oracle (recordRows program)) mapped
  rw [record_map_evaluation,record_map_evaluation] at same
  have rows := congrArg (fun result => result.1.2) same
  have value := congrArg (fun result => result.1.1) same
  refine ⟨?_,?_⟩
  · rw [rows]
    exact canonical_queries_chain oracle height (right++left)
  · rw [canonical_queries_recorded] at value
    exact value

end CommitGolfCandidate.Chained.Native.Refinement
