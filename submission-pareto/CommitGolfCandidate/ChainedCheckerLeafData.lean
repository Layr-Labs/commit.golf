import CommitGolfCandidate.ChainedCheckerLeafRun
import CommitGolfCandidate.ChainedCachedPayload
import CommitGolfCandidate.InputOrder

/-! The delivered leaf queries use submitted values and the decoded 121-bit nonce. -/
namespace CommitGolfCandidate.Chained.Native.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec
open TwoPermutationPrototype TwoPermutationPrototype.Packed TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling SplitCodec
open TwoPermutationPrototype.Packed.RecordLeaf (checkerNonce)
set_option maxRecDepth 8192

theorem checker_loaded_value_byte (input : CheckInput) (ordinal offset : Nat)
    (present : ordinal < input.positions.card) (inside : offset < 256) :
    (Artifact.submission.initialState .check input).getByte
      (BitVec.ofNat 64 (Artifact.submission.layout.values+256*ordinal+offset)) =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))).extractLsb' (8*offset) 8 := by
  have cardinal : input.positions.card≤2^24 := by
    change input.positions.card≤LENGTH
    simpa [Index] using Finset.card_le_univ input.positions
  rw [initial_input_byte Artifact.submission .check input _ (by
    change 6039801952+256*ordinal+offset < 2^64
    omega)]
  have outsideRoot : ¬ (Artifact.submission.layout.commitment ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 6039801952+256*ordinal+offset ∧ 6039801952+256*ordinal+offset < 4294971424)
    omega
  have outsideIndices : ¬ (Artifact.submission.layout.indices ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 6039801952+256*ordinal+offset ∧
      6039801952+256*ordinal+offset < 5905584160+8*input.positions.card)
    omega
  have selected : Artifact.submission.layout.values ≤ Artifact.submission.layout.values+256*ordinal+offset ∧
      Artifact.submission.layout.values+256*ordinal+offset < Artifact.submission.layout.values+(LEAF_SIZE/8)*input.positions.card := by
    change _ ≤ _ ∧ _ < Artifact.submission.layout.values+256*input.positions.card
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, decide_false, selected, and_self, decide_true]
  have quotient : (Artifact.submission.layout.values+256*ordinal+offset-Artifact.submission.layout.values)/(LEAF_SIZE/8) = ordinal := by
    change _ / 256 = _
    omega
  have remainder : (Artifact.submission.layout.values+256*ordinal+offset-Artifact.submission.layout.values)%(LEAF_SIZE/8) = offset := by
    change _ % 256 = _
    omega
  rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]

theorem checker_loaded_value (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    readBuffer (Artifact.submission.initialState .check input)
      (Artifact.submission.layout.values + 256*ordinal) 256 =
      input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present)) := by
  let value := input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
    simpa using present))
  have decoded := read_serialized_slice (Artifact.submission.initialState .check input)
    value (Artifact.submission.layout.values + 256*ordinal) 0 256 (by
      intro j inside
      simpa only [Nat.zero_add] using checker_loaded_value_byte input ordinal j present inside)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem checker_loaded_value_index (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val =
    (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present) := by
  apply Fin.ext
  simpa only [openingIndex, dite_eq_left present] using
    sorted_value_index input.positions ordinal present


def checkerDecodedNonce : InteriorCodec.Record → BitVec 128
  | .cons nonce _ => nonce.setWidth 128

theorem checker_record_raw_nonce_byte (record : InteriorCodec.Record) (index : Nat) (inside : index<16) :
    (rawFieldsBytes (recordRawFields record)).getD index 0=
      (checkerDecodedNonce record).extractLsb' (8*index) 8 := by
  cases record with
  | cons nonce tail =>
    change ((cachedRawField 120 1 nonce 0 (by decide) (by decide)).bytes++_).getD index 0=_
    have length : (cachedRawField 120 1 nonce 0 (by decide) (by decide)).bytes.length=16 := by
      rw [cached_raw_field_bytes 120 1 nonce 0 (by decide) (by decide) (by decide)]
      rfl
    rw [List.getD_append _ _ 0 index (by omega),cached_raw_field_byte 120 1 nonce 0 index
      (by decide) (by decide) (by decide) inside]
    exact (BitVec.extractLsb'_setWidth_of_le (by omega : 8*index+8≤128)).symm

def checkerFirstDecodedRecord (input : CheckInput) : InteriorCodec.Record :=
  decode InteriorCodec.recordSpec (input.proof.take 482)

theorem checker_decoded_head_memory (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    BytesAt s (BitVec.ofNat 64 checkingRawBase) (rawFieldsBytes (recordRawFields (checkerFirstDecodedRecord input))) := by
  obtain ⟨n,count⟩ := Nat.exists_eq_succ_of_ne_zero nonempty
  have memory := ready.memory
  unfold checkerInputRawRecords at memory
  rw [count] at memory
  change BytesAt s _ ((rawFieldsBytes (recordRawFields (checkerFirstDecodedRecord input))++_)++_) at memory
  rw [bytes_at_append,bytes_at_append] at memory
  exact memory.1.1

theorem checker_leaf_nonce_data (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    readBuffer (checkerRecordNonceState s) 12272 16=checkerDecodedNonce (checkerFirstDecodedRecord input) := by
  have bytes (index : Nat) (inside : index<16) :
      (checkerRecordNonceState s).getByte (BitVec.ofNat 64 (12272+index))=
        (checkerDecodedNonce (checkerFirstDecodedRecord input)).extractLsb' (8*index) 8 := by
    rw [checker_record_nonce_byte input footer s ready index inside]
    have bound : index<(rawFieldsBytes (recordRawFields (checkerFirstDecodedRecord input))).length := by
      rw [record_raw_fields_length]; omega
    have memory := checker_decoded_head_memory input nonempty footer s ready index bound
    rw [←BitVec.ofNat_add] at memory
    rw [memory]
    have raw := checker_record_raw_nonce_byte (checkerFirstDecodedRecord input) index inside
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem bound,Option.getD_some] using raw
  have decoded := read_serialized_slice (checkerRecordNonceState s)
    (checkerDecodedNonce (checkerFirstDecodedRecord input)) 12272 0 16 (by
      intro index inside
      simpa only [Nat.zero_add] using bytes index inside)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem checker_leaf_value_byte_frame (input : CheckInput)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) (index : Nat) (inside : index<256) :
    (checkerRecordNonceState s).getByte (BitVec.ofNat 64 (6039801952+index))=
      (Artifact.submission.initialState .check input).getByte (BitVec.ofNat 64 (6039801952+index)) := by
  have fit : checkingRawBase>6039801952+256 := by decide +kernel
  have copy := (checker_copy_bytes .nonce _ checkingRawBase 12272
    (checker_record_nonce_ready input footer s ready) (by decide +kernel)).2
    (BitVec.ofNat 64 (6039801952+index)) (by
      intro offset small
      change offset<16 at small
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega))
  rw [←checker_record_nonce_eq,checker_leaf_head_byte 7 _ (by decide),
    checker_crypto_record_public input footer s ready _ (by omega) (by omega)] at copy
  exact copy

private theorem leaf_buffer_frame (before after : MachineState) (address count : Nat)
    (frame : ∀ index, index<count → after.getByte (BitVec.ofNat 64 (address+index))=
      before.getByte (BitVec.ofNat 64 (address+index))) :
    readBuffer after address count=readBuffer before address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro index inside
  rw [frame index (Finset.mem_range.mp inside)]

theorem checker_leaf_value_data (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    readBuffer (checkerRecordNonceState s) 6039801952 256=
      input.values ((input.positions.attach.sort (fun i j => i.val≤j.val))[0]'(by
        simpa only [Finset.length_sort,Finset.card_attach] using Nat.pos_of_ne_zero nonempty)) := by
  have frame : readBuffer (checkerRecordNonceState s) 6039801952 256=
      readBuffer (Artifact.submission.initialState .check input) 6039801952 256 := by
    exact leaf_buffer_frame _ _ _ _ (checker_leaf_value_byte_frame input footer s ready)
  exact frame.trans (checker_loaded_value input 0 (by omega))

def checkerFirstValueItem (input : CheckInput) (nonempty : input.positions.card≠0) :
    {index // index∈input.positions} :=
  (input.positions.attach.sort (fun i j => i.val≤j.val))[0]'(by
    simpa only [Finset.length_sort,Finset.card_attach] using Nat.pos_of_ne_zero nonempty)

theorem checker_first_value_index (input : CheckInput) (nonempty : input.positions.card≠0) :
    (checkerFirstValueItem input nonempty).val=checkerFirstInputIndex input nonempty :=
  checker_loaded_value_index input 0 (Nat.pos_of_ne_zero nonempty)

private theorem leaf_read_word (s : MachineState) (word : Nat) :
    readBuffer s (8*word) 8=memoryView s word := by
  have slice := read_buffer_slice s (8*word) 32 0 8 (by decide)
  have loaded := read_digest_word s (8*word) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,memoryView,wordAddress] using slice.symm.trans loaded

private theorem leaf_buffer_window (s : MachineState) (start count : Nat) :
    window (memoryView s) start=
      (fun i : Fin count => (readBuffer s (8*start) (8*count)).extractLsb' (64*i.val) 64) := by
  funext i
  change memoryView s (start+i.val)=_
  rw [←leaf_read_word]
  have slice := read_buffer_slice s (8*start) (8*count) (8*i.val) 8 (by have := i.isLt; omega)
  simpa only [Nat.mul_add,←Nat.mul_assoc,Nat.reduceMul] using slice.symm

theorem checker_leaf_value_words (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    window (memoryView (checkerRecordNonceState s)) (754975239+5)=
      (fun i : Fin 32 => (input.values (checkerFirstValueItem input nonempty)).extractLsb' (64*i.val) 64) := by
  rw [leaf_buffer_window]
  change (fun i : Fin 32 => (readBuffer (checkerRecordNonceState s) 6039801952 256).extractLsb' (64*i.val) 64)=_
  rw [checker_leaf_value_data input nonempty footer s ready]
  rfl

theorem checker_leaf_nonce_words (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    checkerNonce (checkerRecordNonceState s)=saltWords (checkerDecodedNonce (checkerFirstDecodedRecord input)) := by
  rw [checker_nonce_words _ 1534 (checker_record_leaf_ready input nonempty footer s ready).proofPointer,
    leaf_buffer_window]
  change (fun i : Fin 2 => (readBuffer (checkerRecordNonceState s) 12272 16).extractLsb' (64*i.val) 64)=_
  rw [checker_leaf_nonce_data input nonempty footer s ready]
  rfl

theorem checker_first_typed_leaf_rows (oracle : Oracle) (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    let message : Words 32 := fun i => (input.values (checkerFirstValueItem input nonempty)).extractLsb' (64*i.val) 64
    let nonce := saltWords (checkerDecodedNonce (checkerFirstDecodedRecord input))
    let a := pinnedFirstRow oracle.permutation message
    let b := pinnedSecondRow oracle.permutation (checkerFirstInputIndex input nonempty) nonce a.2 message
    checkEvaluation oracle (recordRows (leafQueries (checkerRecordNonceState s) 754975239
      (checkerFirstInputIndex input nonempty)))=
      ((secondReplyState (checkerRecordNonceState s) 754975239 a.2 b.2,
        [.permutation a.1 a.2,.permutation b.1 b.2]),2) := by
  rw [checker_leaf_rows,checker_leaf_value_words input nonempty footer s ready,
    checker_leaf_nonce_words input nonempty footer s ready]

theorem checker_first_typed_leaf_digest (oracle : Oracle) (input : CheckInput) (nonempty : input.positions.card≠0)
    (footer : Payload (InteriorCodec.footerSpec (checkerInputFooterNodes input))) (s : MachineState)
    (ready : CheckerDecodedInput input footer s) :
    readBuffer (checkEvaluation oracle (recordRows (leafQueries (checkerRecordNonceState s) 754975239
      (checkerFirstInputIndex input nonempty)))).1.1 12288 32=
      pinnedLeafDigest oracle.permutation (checkerFirstInputIndex input nonempty)
        (saltWords (checkerDecodedNonce (checkerFirstDecodedRecord input)))
        (fun i => (input.values (checkerFirstValueItem input nonempty)).extractLsb' (64*i.val) 64) := by
  rw [checker_first_typed_leaf_rows oracle input nonempty footer s ready]
  exact checker_leaf_digest _ _ _ _

end CommitGolfCandidate.Chained.Native.RecordLeaf
