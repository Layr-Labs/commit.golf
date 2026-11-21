import CommitGolfCandidate.ChainedRecordIteration

/-! Physical raw-stream invariants are maintained by every actual record iteration. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

def rawRecordStream (records : List InteriorCodec.Record) : Proof :=
  records.flatMap fun record => rawFieldsBytes (recordRawFields record)

theorem raw_record_stream_length (records : List InteriorCodec.Record) :
    (rawRecordStream records).length=498*records.length := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    change (rawFieldsBytes (recordRawFields record)++rawRecordStream records).length=_
    rw [List.length_append,record_raw_fields_length,ih,List.length_cons,Nat.mul_add]
    omega

structure RecordStreamReady (records : List InteriorCodec.Record) (footer : Proof)
    (s : MachineState) (source output metadata : Nat) : Prop where
  pc : s.pc=if records=[] then 12380 else 4120
  sourcePointer : s.getReg .x5=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 output
  scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata
  counter : s.getReg .x29=BitVec.ofNat 64 records.length
  memory : BytesAt s (BitVec.ofNat 64 source) (rawRecordStream records++footer)
  ordered : output≤source
  separate : source+498*records.length+footer.length≤metadata
  capacity : metadata+34≤MEMORY_BYTES

theorem record_stream_head (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source output metadata : Nat)
    (ready : RecordStreamReady (record::records) footer s source output metadata) :
    RawFieldsReady (recordRawFields record) (rawRecordStream records++footer) [] []
      (recordResetPrefix s 3) source output metadata := by
  apply record_reset_ready record _ s source output metadata ready.sourcePointer ready.outputPointer ready.scratch
  · simpa only [rawRecordStream,List.flatMap_cons,List.append_assoc] using ready.memory
  · exact ready.ordered
  · have bound := ready.separate
    simp only [List.length_cons,Nat.mul_add] at bound
    rw [List.length_append,raw_record_stream_length]
    omega
  · exact ready.capacity

theorem record_stream_step (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source output metadata : Nat)
    (ready : RecordStreamReady (record::records) footer s source output metadata) :
    RecordStreamReady records footer (recordIterationState record s) (source+498) (output+482) metadata := by
  have head := record_stream_head record records footer s source output metadata ready
  have bodyPC : (recordResetPrefix s 3).pc=4132 := by
    rw [record_reset_pc _ 3 (by decide),ready.pc]
    rfl
  have packedPC := record_pack_pc record _ _ source output metadata head ready.capacity bodyPC
  have count : (recordPackedState record (recordResetPrefix s 3)).getReg .x29=
      BitVec.ofNat 64 (records.length+1) := by
    rw [record_pack_control _ _ .x29 (by simp),record_reset_register _ .x29 (by decide),ready.counter]
    rfl
  have fit : records.length<2^64 := by
    have bound := ready.separate
    have capacity := ready.capacity
    simp only [List.length_cons] at bound
    unfold MEMORY_BYTES at capacity
    omega
  constructor
  · rw [recordIterationState,record_post_pc _ packedPC,record_post_done _ _ fit count]
    cases records <;> rfl
  · rw [recordIterationState,record_post_register,record_post_prefix_register _ .x5 (by decide) (by decide)]
    exact record_pack_source record _ _ source output metadata head
  · rw [recordIterationState,record_post_register,record_post_output]
    exact record_pack_cursor record _ _ source output metadata head ready.capacity
  · rw [recordIterationState,record_post_register,record_post_prefix_register _ .x17 (by decide) (by decide),
      record_pack_control _ _ .x17 (by simp),record_reset_register _ .x17 (by decide)]
    exact ready.scratch
  · exact record_post_counter _ records.length count
  · intro index inside
    rw [recordIterationState,record_post_byte]
    exact record_pack_future record _ _ source output metadata head ready.capacity index inside
  · have ordered := ready.ordered
    omega
  · have bound := ready.separate
    simp only [List.length_cons,Nat.mul_add] at bound
    omega
  · exact ready.capacity

end CommitGolfCandidate.Chained.Native
