import CommitGolfCandidate.ChainedFooterComplete

/-! The complete record loop preserves all low-address cap mark words. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem record_loop_byte_below (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source output metadata address : Nat) (ready : RecordStreamReady records footer s source output metadata)
    (below : address<output) :
    (recordLoopState records s).getByte (BitVec.ofNat 64 address)=s.getByte (BitVec.ofNat 64 address) := by
  let past : Proof := List.ofFn fun index : Fin output => s.getByte (BitVec.ofNat 64 index.val)
  have initial : BytesAt s (BitVec.ofNat 64 0) past := by
    intro index inside
    have access : past.getD index 0=s.getByte (BitVec.ofNat 64 index) := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside]
      simp only [past,List.getElem_ofFn,Option.getD_some]
    rw [access]
    change s.getByte (0#64+BitVec.ofNat 64 index)=_
    rw [BitVec.zero_add]
  have preserved := record_loop_prefix records footer past s source output metadata 0 ready initial (by simp only [past,List.length_ofFn,Nat.zero_add])
  have body := ((bytes_at_append _ _ past (encodedRecords records)).mp preserved).1
  have access : address<past.length := by simpa only [past,List.length_ofFn] using below
  have value := body address access
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem access] at value
  simpa only [past,List.getElem_ofFn,Option.getD_some,BitVec.zero_add] using value

theorem record_loop_mark_frame (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source output metadata node : Nat) (ready : RecordStreamReady records footer s source output metadata)
    (above : 8192≤output) (bound : node<512) :
    (recordLoopState records s).getMem (BitVec.ofNat 64 (4096+8*node))=s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  apply aligned_word_of_byte_frame s _ _ (by omega)
  intro index inside
  exact record_loop_byte_below records footer s source output metadata _ ready (by omega)

theorem record_loop_proof_base (records : List InteriorCodec.Record) (s : MachineState) :
    (recordLoopState records s).getReg .x17=s.getReg .x17 := by
  induction records generalizing s with
  | nil => rw [record_loop_zero]
  | cons record records ih =>
    rw [record_loop_cons,ih,recordIterationState,record_post_register,
      record_post_prefix_register _ .x17 (by decide) (by decide),record_pack_control _ _ .x17 (by simp),
      record_reset_register _ .x17 (by decide)]

theorem raw_field_byte_frame (field : RawField) (s : MachineState) (query : Word)
    (output : ∀ index, index<field.low.length → query≠s.getReg .x6+BitVec.ofNat 64 index)
    (metadata : query≠s.getReg .x7 ∧ query≠s.getReg .x7+1) :
    (field.state s).getByte query=s.getByte query := by
  rw [RawField.state,preparedFieldState,fieldBuildState,field_descriptor_byte,
    low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),
    field_header_frame _ _ _ .x7 (by decide) (by decide),
    ite_eq_right metadata.2,ite_eq_right metadata.1,low_copy_byte_frame]
  · exact field_header_byte _ _ s query
  · intro index inside
    rw [field_header_frame _ _ _ .x6 (by decide) (by decide)]
    exact output index inside

theorem raw_fields_byte_below (fields : List RawField) (s : MachineState) (output metadata query : Nat)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (outputRoom : output+(rawFieldsLow fields).length≤MEMORY_BYTES)
    (metaRoom : metadata+2*fields.length≤MEMORY_BYTES)
    (belowOutput : query<output) (belowMetadata : query<metadata) :
    (rawFieldsState fields s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  induction fields generalizing s output metadata with
  | nil => rw [raw_fields_zero]
  | cons field fields ih =>
    have lowLength : (rawFieldsLow (field::fields)).length=field.low.length+(rawFieldsLow fields).length := by
      simp only [rawFieldsLow,List.flatMap_cons,List.length_append]
    have firstOutput : (field.state s).getReg .x6=BitVec.ofNat 64 (output+field.low.length) := by
      rw [(raw_field_control field s).2.1,outputPointer,←BitVec.ofNat_add]
    have firstMeta : (field.state s).getReg .x7=BitVec.ofNat 64 (metadata+2) := by
      rw [(raw_field_control field s).2.2,metaPointer]
      change BitVec.ofNat 64 metadata+BitVec.ofNat 64 2=_
      rw [←BitVec.ofNat_add]
    rw [raw_fields_cons,ih _ (output+field.low.length) (metadata+2) firstOutput firstMeta
      (by omega) (by simp only [List.length_cons] at metaRoom; omega) (by omega) (by omega)]
    apply raw_field_byte_frame
    · intro index inside
      rw [outputPointer,←BitVec.ofNat_add]
      apply word_of_nat_ne _ _ <;> unfold MEMORY_BYTES at outputRoom <;> omega
    · rw [metaPointer]
      constructor
      · apply word_of_nat_ne _ _ <;> unfold MEMORY_BYTES at metaRoom <;> simp only [List.length_cons] at metaRoom <;> omega
      · change BitVec.ofNat 64 query≠BitVec.ofNat 64 metadata+BitVec.ofNat 64 1
        rw [←BitVec.ofNat_add]
        apply word_of_nat_ne _ _ <;> unfold MEMORY_BYTES at metaRoom <;> simp only [List.length_cons] at metaRoom <;> omega

theorem tail_step_byte_frame (s : MachineState) (query : Word) (apart : query≠s.getReg .x20) :
    (tailStepState s).getByte query=s.getByte query := by
  have back (state : MachineState) : (tailBackEdge state).getByte query=state.getByte query := by
    simp only [MachineState.getByte,tail_back_memory]
  rw [tailStepState,back]
  change (tailEmitState (tailLoadPrefix s 3)).getByte query=_
  rw [tail_emit_byte,tail_load_frame _ .x20 (by decide) (by decide) (by decide)]
  have loaded : (tailLoadPrefix s 3).getByte query=s.getByte query := rfl
  split <;> simp only [loaded,ite_eq_right apart]

theorem tail_fields_byte_below (n : Nat) (s : MachineState) (output query : Nat)
    (outputPointer : s.getReg .x20=BitVec.ofNat 64 output)
    (outputRoom : output+n+1≤MEMORY_BYTES) (below : query<output) :
    (tailFieldsState n s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  induction n generalizing s output with
  | zero => rw [tail_fields_state_zero]
  | succ n ih =>
    obtain ⟨increment,bound,pointer⟩ := tail_step_output_increment s
    rw [outputPointer,←BitVec.ofNat_add] at pointer
    rw [tailFieldsState,ih _ (output+increment) pointer (by omega) (by omega)]
    apply tail_step_byte_frame
    rw [outputPointer]
    apply word_of_nat_ne _ _ <;> unfold MEMORY_BYTES at outputRoom <;> omega

theorem tail_fields_output_increment (n : Nat) (s : MachineState) :
    ∃ increment : Nat, increment≤n ∧
      (tailFieldsState n s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 increment := by
  induction n generalizing s with
  | zero => exact ⟨0,by omega,by rw [tailFieldsState]; exact (BitVec.add_zero _).symm⟩
  | succ n ih =>
    obtain ⟨first,firstBound,firstPointer⟩ := tail_step_output_increment s
    obtain ⟨rest,restBound,restPointer⟩ := ih (tailStepState s)
    refine ⟨first+rest,by omega,?_⟩
    rw [tailFieldsState,restPointer,firstPointer,BitVec.add_assoc,←BitVec.ofNat_add]

theorem tail_traverse_byte_below (n : Nat) (s : MachineState) (output query : Nat)
    (outputPointer : s.getReg .x20=BitVec.ofNat 64 output)
    (outputRoom : output+n+1≤MEMORY_BYTES) (below : query<output) :
    (tailTraverseState n s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  have entryPointer : (tailEntryState s).getReg .x20=BitVec.ofNat 64 output := by
    rw [tail_entry_register,outputPointer]
  have fieldFrame := tail_fields_byte_below n (tailEntryState s) output query entryPointer outputRoom below
  obtain ⟨increment,bound,pointer⟩ := tail_fields_output_increment n (tailEntryState s)
  rw [entryPointer,←BitVec.ofNat_add] at pointer
  rw [tailTraverseState,tail_finish_byte]
  have apart : BitVec.ofNat 64 query≠(tailFieldsState n (tailEntryState s)).getReg .x20 := by
    rw [pointer]
    apply word_of_nat_ne _ _ <;> unfold MEMORY_BYTES at outputRoom <;> omega
  have entryByte : (tailEntryState s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
    simp only [MachineState.getByte,tail_entry_memory]
  split <;> simp only [ite_eq_right apart,fieldFrame,entryByte]

theorem tail_traverse_output_increment (n : Nat) (s : MachineState) :
    ∃ increment : Nat, increment≤n+1 ∧
      (tailTraverseState n s).getReg .x20=s.getReg .x20+BitVec.ofNat 64 increment := by
  obtain ⟨fields,fieldsBound,fieldsPointer⟩ := tail_fields_output_increment n (tailEntryState s)
  obtain ⟨last,lastBound,lastPointer⟩ := tail_finish_output_increment (tailFieldsState n (tailEntryState s))
  refine ⟨fields+last,by omega,?_⟩
  rw [tailTraverseState,lastPointer,fieldsPointer,tail_entry_register,BitVec.add_assoc,←BitVec.ofNat_add]

theorem record_iteration_output_increment (record : InteriorCodec.Record) (s : MachineState) :
    ∃ increment : Nat, increment≤497 ∧
      (recordIterationState record s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 increment := by
  have lowSize : (rawFieldsLow (recordRawFields record)).length=479 := by
    rw [recordRawFields,payload_raw_fields_low,(record_descriptor_sizes record).1]
  obtain ⟨increment,bound,pointer⟩ := tail_traverse_output_increment 17 (recordTailState record (recordResetPrefix s 3))
  refine ⟨479+increment,by omega,?_⟩
  rw [recordIterationState,record_post_register,record_post_output,recordPackedState,pointer,
    recordTailState,record_tail_setup_cursor,(raw_fields_control _ _).2.1,lowSize,
    record_reset_register _ .x6 (by decide),BitVec.add_assoc,←BitVec.ofNat_add]

theorem record_pack_range_byte_below (record : InteriorCodec.Record) (s : MachineState) (output metadata query : Nat)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (outputRoom : output+497≤MEMORY_BYTES) (metaRoom : metadata+34≤MEMORY_BYTES)
    (belowOutput : query<output) (belowMetadata : query<metadata) :
    (recordPackedState record s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  have lowSize : (rawFieldsLow (recordRawFields record)).length=479 := by
    rw [recordRawFields,payload_raw_fields_low,(record_descriptor_sizes record).1]
  have pointer : (recordTailState record s).getReg .x20=BitVec.ofNat 64 (output+479) := by
    rw [recordTailState,record_tail_setup_cursor,(raw_fields_control _ _).2.1,outputPointer,lowSize,←BitVec.ofNat_add]
  rw [recordPackedState,tail_traverse_byte_below 17 _ (output+479) query pointer (by omega) (by omega),
    recordTailState,record_tail_setup_byte]
  apply raw_fields_byte_below _ s output metadata query outputPointer metaPointer
    (by rw [lowSize]; omega) (by simpa only [record_raw_fields_count] using metaRoom) belowOutput belowMetadata

theorem record_iteration_range_byte_below (record : InteriorCodec.Record) (s : MachineState) (output metadata query : Nat)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (outputRoom : output+497≤MEMORY_BYTES) (metaRoom : metadata+34≤MEMORY_BYTES)
    (belowOutput : query<output) (belowMetadata : query<metadata) :
    (recordIterationState record s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  rw [recordIterationState,record_post_byte,record_pack_range_byte_below record _ output metadata query
    (by rw [record_reset_register _ .x6 (by decide),outputPointer])
    (by rw [record_reset_metadata,scratch]) outputRoom metaRoom belowOutput belowMetadata,record_reset_byte]

theorem record_loop_range_byte_below (records : List InteriorCodec.Record) (s : MachineState) (output metadata query : Nat)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (outputRoom : output+497*records.length≤MEMORY_BYTES) (metaRoom : metadata+34≤MEMORY_BYTES)
    (belowOutput : query<output) (belowMetadata : query<metadata) :
    (recordLoopState records s).getByte (BitVec.ofNat 64 query)=s.getByte (BitVec.ofNat 64 query) := by
  induction records generalizing s output with
  | nil => rw [record_loop_zero]
  | cons record records ih =>
    obtain ⟨increment,bound,pointer⟩ := record_iteration_output_increment record s
    rw [outputPointer,←BitVec.ofNat_add] at pointer
    have nextScratch : (recordIterationState record s).getReg .x17+0x200000000=BitVec.ofNat 64 metadata := by
      rw [recordIterationState,record_post_register,record_post_prefix_register _ .x17 (by decide) (by decide),
        record_pack_control _ _ .x17 (by simp),record_reset_register _ .x17 (by decide),scratch]
    have room : output+497≤MEMORY_BYTES := by simp only [List.length_cons] at outputRoom; omega
    have nextRoom : output+increment+497*records.length≤MEMORY_BYTES := by
      simp only [List.length_cons] at outputRoom; omega
    rw [record_loop_cons,ih _ (output+increment) pointer nextScratch nextRoom (by omega)]
    exact record_iteration_range_byte_below record s output metadata query outputPointer scratch room metaRoom belowOutput belowMetadata

theorem record_loop_range_mark_frame (records : List InteriorCodec.Record) (s : MachineState) (output metadata node : Nat)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (outputRoom : output+497*records.length≤MEMORY_BYTES) (metaRoom : metadata+34≤MEMORY_BYTES)
    (outputAbove : 8192≤output) (metaAbove : 8192≤metadata) (bound : node<512) :
    (recordLoopState records s).getMem (BitVec.ofNat 64 (4096+8*node))=s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  apply aligned_word_of_byte_frame s _ _ (by omega)
  intro index inside
  exact record_loop_range_byte_below records s output metadata _ outputPointer scratch outputRoom metaRoom (by omega) (by omega)

end CommitGolfCandidate.Chained.Native
