import CommitGolfCandidate.ChainedRecordStream

/-! Completed records survive compaction and packing of the next record. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem record_pack_past (record : InteriorCodec.Record) (suffix past : Proof) (s : MachineState)
    (source output metadata base : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) (previous : BytesAt s (BitVec.ofNat 64 base) past)
    (endpoint : base+past.length=output) :
    BytesAt (recordPackedState record s) (BitVec.ofNat 64 base) past := by
  have general : RawFieldsReady (recordRawFields record) suffix past [] s source base metadata := by
    refine ⟨input.sourcePointer,?_,input.metaPointer,input.input,previous,input.metadata,?_,input.separate,input.room⟩
    · simpa only [endpoint,List.length_nil,Nat.add_zero] using input.outputPointer
    · rw [endpoint]
      simpa using input.ordered
  have built := opening_record_build_memory record suffix past [] s source base metadata general
  have earlier := ((bytes_at_append _ _ past (lowBytes record)).mp built.output).1
  have ready := record_tail_ready record suffix s source output metadata input capacity
  have rows : BytesAt (tailEntryState (recordTailState record s))
      ((tailEntryState (recordTailState record s)).getReg .x21) (descriptorBytes (highRows record)) := by
    intro index inside
    rw [tail_entry_register,ready.source]
    simp only [MachineState.getByte,tail_entry_memory]
    exact ready.rows index inside
  have apart : TailApart ((tailEntryState (recordTailState record s)).getReg .x21)
      ((tailEntryState (recordTailState record s)).getReg .x20) (highRows record) := by
    simpa only [tail_entry_register] using ready.apart
  intro index inside
  change (tailFinishState (tailFieldsState 17 (tailEntryState (recordTailState record s)))).getByte _=_
  rw [native_record_tail_memory record _ (record_tail_entry_buffer record s) rows apart,write_byte_list_preserves]
  · have entryByte (query : Word) : (tailEntryState (recordTailState record s)).getByte query=
        (recordTailState record s).getByte query := by simp only [MachineState.getByte,tail_entry_memory]
    rw [entryByte,recordTailState,record_tail_setup_byte]
    exact earlier index inside
  · intro offset bounded
    have tailLength : (packedBits (highs record)).length=3 := by
      simpa only [high_rows_flatten] using (record_descriptor_sizes record).2.1
    rw [tailLength] at bounded
    rw [tail_entry_register,ready.cursor,←BitVec.ofNat_add,←BitVec.ofNat_add]
    have ordered := input.ordered
    have separate := input.separate
    simp only [List.length_nil,Nat.add_zero,record_raw_fields_length] at ordered separate
    unfold MEMORY_BYTES at capacity
    apply word_of_nat_ne <;> omega

theorem record_iteration_prefix (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer past : Proof) (s : MachineState) (source output metadata base : Nat)
    (ready : RecordStreamReady (record::records) footer s source output metadata)
    (previous : BytesAt s (BitVec.ofNat 64 base) past) (endpoint : base+past.length=output) :
    BytesAt (recordIterationState record s) (BitVec.ofNat 64 base) (past++encode record) := by
  have input := record_stream_head record records footer s source output metadata ready
  have previousReset : BytesAt (recordResetPrefix s 3) (BitVec.ofNat 64 base) past := by
    intro index inside
    rw [record_reset_byte]
    exact previous index inside
  have earlier := record_pack_past record _ past (recordResetPrefix s 3) source output metadata base
    input ready.capacity previousReset endpoint
  have current := record_pack_memory record _ (recordResetPrefix s 3) source output metadata input ready.capacity
  apply (bytes_at_append _ _ past (encode record)).mpr
  constructor
  · intro index inside
    rw [recordIterationState,record_post_byte]
    exact earlier index inside
  · rw [←BitVec.ofNat_add,endpoint]
    intro index inside
    rw [recordIterationState,record_post_byte]
    exact current index inside

end CommitGolfCandidate.Chained.Native
