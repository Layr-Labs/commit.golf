import CommitGolfCandidate.ChainedRecordTailSetup

/-! Construct and pack one record with actual standalone instructions and derived access safety. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
attribute [local irreducible] execute

def recordTailState (record : InteriorCodec.Record) (s : MachineState) : MachineState :=
  recordTailSetupPrefix (rawFieldsState (recordRawFields record) s) 6
def recordPackedState (record : InteriorCodec.Record) (s : MachineState) : MachineState :=
  tailTraverseState 17 (recordTailState record s)
def recordPackCycles (record : InteriorCodec.Record) (s : MachineState) : Nat :=
  2035+6+tailTraverseCycles 17 (recordTailState record s)

structure RecordTailReady (record : InteriorCodec.Record) (s : MachineState) (output metadata : Nat) : Prop where
  buffer : TailBuffer s []
  cursor : s.getReg .x20=BitVec.ofNat 64 (output+479)
  source : s.getReg .x21=BitVec.ofNat 64 metadata
  count : s.getReg .x22=17
  body : BytesAt s (BitVec.ofNat 64 output) (lowBytes record)
  rows : BytesAt s (BitVec.ofNat 64 metadata) (descriptorBytes (highRows record))
  apart : TailApart (s.getReg .x21) (s.getReg .x20) (highRows record)
  ready : TailFieldsReady 17 (tailEntryState s)
  access : accessValid ((tailFieldsState 17 (tailEntryState s)).getReg .x20) 1=true

theorem record_tail_ready (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) : RecordTailReady record (recordTailState record s) output metadata := by
  have built := opening_record_build_memory record suffix [] [] s source output metadata input
  have out : (rawFieldsState (recordRawFields record) s).getReg .x6=BitVec.ofNat 64 (output+479) := by
    simpa only [List.nil_append,(record_descriptor_sizes record).1] using built.outputPointer
  have metaPointer : (rawFieldsState (recordRawFields record) s).getReg .x7=BitVec.ofNat 64 (metadata+34) := by
    simpa only [List.nil_append,(record_descriptor_sizes record).2.2] using built.metaPointer
  have cursor : (recordTailState record s).getReg .x20=BitVec.ofNat 64 (output+479) := by
    rw [recordTailState,record_tail_setup_cursor,out]
  have table : (recordTailState record s).getReg .x21=BitVec.ofNat 64 metadata := by
    rw [recordTailState,record_tail_setup_source,metaPointer]
    have constant : (34 : Word)=BitVec.ofNat 64 34 := by decide
    rw [constant]
    simpa only [Nat.add_sub_cancel] using
      BitVec.ofNat_sub_ofNat_of_le (metadata+34) 34 (by decide) (by omega)
  have body : BytesAt (recordTailState record s) (BitVec.ofNat 64 output) (lowBytes record) := by
    intro index inside
    rw [recordTailState,record_tail_setup_byte]
    exact built.output index inside
  have rows : BytesAt (recordTailState record s) (BitVec.ofNat 64 metadata) (descriptorBytes (highRows record)) := by
    intro index inside
    rw [recordTailState,record_tail_setup_byte]
    exact built.metadata index inside
  have ordered := input.ordered
  have separate := input.separate
  simp only [List.length_nil,Nat.add_zero,record_raw_fields_length] at ordered separate
  have gap : output+479+(highRows record).length<metadata := by
    rw [high_rows_length]
    change output+479+17<metadata
    omega
  have room : metadata+2*(highRows record).length≤MEMORY_BYTES := by
    rw [high_rows_length]
    exact capacity
  have apart : TailApart ((recordTailState record s).getReg .x21)
      ((recordTailState record s).getReg .x20) (highRows record) := by
    rw [table,cursor]
    exact tail_apart_of_ranges metadata (output+479) _ gap room
  have buffer := record_tail_setup_buffer (rawFieldsState (recordRawFields record) s)
  have entryBuffer : TailBuffer (tailEntryState (recordTailState record s)) [] := by
    constructor
    · simpa only [tail_entry_register,recordTailState] using buffer.value
    · simpa only [tail_entry_register,recordTailState] using buffer.count
    · simpa only [tail_entry_register,recordTailState] using buffer.eight
    · exact buffer.pending
  have entryRows : BytesAt (tailEntryState (recordTailState record s))
      ((tailEntryState (recordTailState record s)).getReg .x21) (descriptorBytes (highRows record)) := by
    intro index inside
    rw [tail_entry_register,table]
    simp only [MachineState.getByte,tail_entry_memory]
    exact rows index inside
  have access := tail_rows_access (highRows record) [] (tailEntryState (recordTailState record s))
    metadata (output+479) entryBuffer (high_rows_small record record_fields_small) entryRows
    (by rw [tail_entry_register,table]) (by rw [tail_entry_register,cursor])
    (by rw [tail_entry_register,recordTailState,record_tail_setup_count,high_rows_length]; rfl)
    gap room (by rw [high_rows_length]; change output+479+17+1≤MEMORY_BYTES; omega)
  simp only [high_rows_length] at access
  exact ⟨buffer,cursor,table,record_tail_setup_count _,body,rows,apart,access.1,access.2⟩

theorem record_pack_memory (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) :
    BytesAt (recordPackedState record s) (BitVec.ofNat 64 output) (encode record) := by
  have ready := record_tail_ready record suffix s source output metadata input capacity
  apply native_traverse_payload_bytes_at record _ _ (by decide +kernel) record_fields_small ready.buffer
  · rw [(record_descriptor_sizes record).1,←BitVec.ofNat_add]
    exact ready.cursor
  · exact ready.body
  · rw [ready.source]
    exact ready.rows
  · exact ready.apart
  · rw [InteriorCodec.encode_record_length]; decide

theorem record_pack_execution (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat)
    (input : RawFieldsReady (recordRawFields record) suffix [] [] s source output metadata)
    (capacity : metadata+34≤MEMORY_BYTES) (pc : s.pc=4132) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (recordPackCycles record s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordPackedState record s) coins
          return result.charge (recordPackCycles record s) 0) := by
  have ready := record_tail_ready record suffix s source output metadata input capacity
  have code := controller_record_tail_at openingControllerImage 4096 opening_controller_ops_at
  have bodyPC : (rawFieldsState (recordRawFields record) s).pc=12272 := by
    rw [raw_fields_end_pc,record_raw_fields_steps,pc]
    rfl
  have tailPC : (recordTailState record s).pc=12296 := by
    rw [recordTailState,record_tail_setup_pc _ 6 (by decide),bodyPC]
    rfl
  have count : tailNoFields (recordTailState record s)=decide (17=0) := by
    rw [tailNoFields,ready.count]
    rfl
  rw [show recordPackCycles record s+fuel=2035+(6+(tailTraverseCycles 17 (recordTailState record s)+fuel)) by
    unfold recordPackCycles; omega,
    opening_record_build_execution record suffix [] [] s source output metadata input pc
      (by simpa using capacity),
    record_tail_setup_execution openingControllerImage 12272 code.1 _ bodyPC]
  simp only [bind_assoc,pure_bind]
  change (do let result ← execute openingControllerImage (tailTraverseCycles 17 (recordTailState record s)+fuel)
               (recordTailState record s) coins
             return (result.charge 6 0).charge 2035 0)=_
  rw [tail_traverse_execution openingControllerImage 12296 code.2 _ _ tailPC count ready.ready (fun _ => ready.access)]
  simp [recordPackCycles,recordPackedState,recordTailState,Execution.charge,Nat.add_assoc]
  congr 1
  funext result
  congr 1
  omega

theorem record_pack_bound (record : InteriorCodec.Record) (s : MachineState) : recordPackCycles record s≤2266 := by
  have bound := tail_traverse_bound 17 (recordTailState record s)
  unfold recordPackCycles
  omega

end CommitGolfCandidate.Chained.Native
