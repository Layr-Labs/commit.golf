import CommitGolfCandidate.ChainedRecordPacking
import CommitGolfCandidate.ChainedTraversalFrame

/-! Record packing preserves controller registers and unread input and advances the exact output cursor. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec

theorem record_pack_control (record : InteriorCodec.Record) (s : MachineState) (reg : Reg)
    (control : reg=.x4 ∨ reg=.x8 ∨ reg=.x16 ∨ reg=.x17 ∨ reg=.x19 ∨ reg=.x29 ∨ reg=.x30 ∨ reg=.x31) :
    (recordPackedState record s).getReg reg=s.getReg reg := by
  rcases control with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [recordPackedState,tail_traverse_register _ _ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),recordTailState,
      record_tail_setup_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      raw_fields_register _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem record_pack_source (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata) :
    (recordPackedState record s).getReg .x5=BitVec.ofNat 64 (source+498) := by
  rw [recordPackedState,tail_traverse_register _ _ _ (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide),recordTailState,
    record_tail_setup_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact (opening_record_build_memory record suffix [] [] s source output metadata input).sourcePointer

theorem record_tail_entry_buffer (record : InteriorCodec.Record) (s : MachineState) :
    TailBuffer (tailEntryState (recordTailState record s)) [] := by
  have buffer := record_tail_setup_buffer (rawFieldsState (recordRawFields record) s)
  constructor
  · simpa only [tail_entry_register,recordTailState] using buffer.value
  · simpa only [tail_entry_register,recordTailState] using buffer.count
  · simpa only [tail_entry_register,recordTailState] using buffer.eight
  · exact buffer.pending

theorem record_pack_cursor (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) :
    (recordPackedState record s).getReg .x20=BitVec.ofNat 64 (output+482) := by
  have ready := record_tail_ready record suffix s source output metadata input capacity
  have memory : BytesAt (tailEntryState (recordTailState record s))
      ((tailEntryState (recordTailState record s)).getReg .x21) (descriptorBytes (highRows record)) := by
    intro index inside
    rw [tail_entry_register,ready.source]
    simp only [MachineState.getByte,tail_entry_memory]
    exact ready.rows index inside
  have apart : TailApart ((tailEntryState (recordTailState record s)).getReg .x21)
      ((tailEntryState (recordTailState record s)).getReg .x20) (highRows record) := by
    simpa only [tail_entry_register] using ready.apart
  have pointer := native_tail_cursor (highRows record) [] (tailEntryState (recordTailState record s))
    (record_tail_entry_buffer record s) (high_rows_small record record_fields_small) memory apart
  simp only [high_rows_length,List.nil_append,tail_entry_register,ready.cursor,(record_descriptor_sizes record).2.1] at pointer
  change (recordPackedState record s).getReg .x20=BitVec.ofNat 64 (output+479)+BitVec.ofNat 64 3 at pointer
  rw [pointer,←BitVec.ofNat_add]

theorem record_pack_pc (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) (pc : s.pc=4132) :
    (recordPackedState record s).pc=12364 := by
  have ready := record_tail_ready record suffix s source output metadata input capacity
  have bodyPC : (rawFieldsState (recordRawFields record) s).pc=12272 := by
    rw [raw_fields_end_pc,record_raw_fields_steps,pc]
    rfl
  have tailPC : (recordTailState record s).pc=12296 := by
    rw [recordTailState,record_tail_setup_pc _ 6 (by decide),bodyPC]
    rfl
  have entryPC : (tailEntryState (recordTailState record s)).pc=
      if 17=0 then (12296 : Word)+56 else 12296+4 := by
    rw [tail_entry_pc,tailPC,tailNoFields,ready.count]
    rfl
  exact tail_fields_finish_pc 17 _ 12296 entryPC ready.ready

theorem record_pack_future (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) :
    BytesAt (recordPackedState record s) (BitVec.ofNat 64 (source+498)) suffix := by
  have ready := record_tail_ready record suffix s source output metadata input capacity
  have built := opening_record_build_memory record suffix [] [] s source output metadata input
  have memory : BytesAt (tailEntryState (recordTailState record s))
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
  rw [native_record_tail_memory record _ (record_tail_entry_buffer record s) memory apart,write_byte_list_preserves]
  · have entryByte (query : Word) : (tailEntryState (recordTailState record s)).getByte query=
        (recordTailState record s).getByte query := by simp only [MachineState.getByte,tail_entry_memory]
    rw [entryByte,recordTailState,record_tail_setup_byte]
    exact built.input index inside
  · intro offset bounded
    have tailLength : (packedBits (highs record)).length=3 := by
      simpa only [high_rows_flatten] using (record_descriptor_sizes record).2.1
    rw [tail_entry_register,ready.cursor,←BitVec.ofNat_add,←BitVec.ofNat_add]
    have ordered := input.ordered
    have separate := input.separate
    have room := input.room
    simp only [record_raw_fields_length,List.length_nil,Nat.add_zero,record_raw_fields_count] at ordered separate room
    rw [tailLength] at bounded
    apply word_of_nat_ne
    · omega
    · omega
    · omega

theorem record_pack_range_execution (record : InteriorCodec.Record) (s : MachineState)
    (source output metadata : Nat) (pc : s.pc=4132)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata)
    (sourceRoom : source+498≤MEMORY_BYTES)
    (outputRoom : output+497≤MEMORY_BYTES)
    (metaRoom : metadata+34≤MEMORY_BYTES) :
    (∀ fuel coins, execute openingControllerImage (recordPackCycles record s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordPackedState record s) coins
          return result.charge (recordPackCycles record s) 0)) ∧
    (recordPackedState record s).pc=12364 ∧
    (recordPackedState record s).getReg .x5=BitVec.ofNat 64 (source+498) ∧
    ∃ increment : Nat, increment≤497 ∧
      (recordPackedState record s).getReg .x20=BitVec.ofNat 64 (output+increment) := by
  have lowSize : (rawFieldsLow (recordRawFields record)).length=479 := by
    rw [recordRawFields,payload_raw_fields_low,(record_descriptor_sizes record).1]
  obtain ⟨builtSource,builtOutput,builtMetadata⟩ := raw_fields_control (recordRawFields record) s
  rw [sourcePointer,record_raw_fields_length,←BitVec.ofNat_add] at builtSource
  rw [outputPointer,lowSize,←BitVec.ofNat_add] at builtOutput
  rw [metaPointer,record_raw_fields_count,←BitVec.ofNat_add] at builtMetadata
  have bodyPC : (rawFieldsState (recordRawFields record) s).pc=12272 := by
    rw [raw_fields_end_pc,record_raw_fields_steps,pc]
    rfl
  have tailPC : (recordTailState record s).pc=12296 := by
    rw [recordTailState,record_tail_setup_pc _ 6 (by decide),bodyPC]
    rfl
  have table : (recordTailState record s).getReg .x21=BitVec.ofNat 64 metadata := by
    rw [recordTailState,record_tail_setup_source,builtMetadata]
    have constant : (34 : Word)=BitVec.ofNat 64 34 := by decide
    rw [constant]
    simpa only [Nat.add_sub_cancel] using
      BitVec.ofNat_sub_ofNat_of_le (metadata+34) 34 (by decide) (by omega)
  have cursor : (recordTailState record s).getReg .x20=BitVec.ofNat 64 (output+479) := by
    rw [recordTailState,record_tail_setup_cursor,builtOutput]
  have count : (recordTailState record s).getReg .x22=BitVec.ofNat 64 17 := by
    rw [recordTailState,record_tail_setup_count]
    rfl
  have code := controller_record_tail_at openingControllerImage 4096 opening_controller_ops_at
  obtain ⟨tailRun,tailEnd,increment,incrementBound,tailOutput⟩ :=
    tail_traverse_range_execution openingControllerImage 12296 code.2 17 (recordTailState record s)
      metadata (output+479) tailPC table cursor count (by omega) (by omega)
  refine ⟨?_,tailEnd,?_,479+increment,by omega,?_⟩
  · intro fuel coins
    have buildRun := raw_fields_range_execution openingControllerImage (recordRawFields record) s
      source output metadata 4132 (opening_record_fields_at record) pc sourcePointer outputPointer metaPointer
      (by simpa only [record_raw_fields_length] using sourceRoom)
      (by rw [lowSize]; omega) (by simpa only [record_raw_fields_count] using metaRoom)
      (6+(tailTraverseCycles 17 (recordTailState record s)+fuel)) coins
    rw [record_raw_fields_steps] at buildRun
    rw [show recordPackCycles record s+fuel=
      2035+(6+(tailTraverseCycles 17 (recordTailState record s)+fuel)) by
        unfold recordPackCycles; omega,buildRun,
      record_tail_setup_execution openingControllerImage 12272 code.1 _ bodyPC]
    simp only [bind_assoc]
    change (do let result ← execute openingControllerImage (tailTraverseCycles 17 (recordTailState record s)+fuel)
                 (recordTailState record s) coins
               return (result.charge 6 0).charge 2035 0)=_
    rw [tailRun]
    simp [recordPackCycles,recordPackedState,Execution.charge,Nat.add_assoc]
    congr 1
    funext result
    congr 1
    omega
  · rw [recordPackedState,tail_traverse_register _ _ .x5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),recordTailState,
      record_tail_setup_frame _ .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact builtSource
  · simpa only [recordPackedState,Nat.add_assoc] using tailOutput

end CommitGolfCandidate.Chained.Native
