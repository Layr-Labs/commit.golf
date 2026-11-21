import CommitGolfCandidate.ChainedCheckerRecordInverseRun
import CommitGolfCandidate.ChainedCheckerRecordAdvance
import CommitGolfCandidate.ChainedRecordLoop

section

/-! Complete record decoding preserves bytes outside its raw and metadata writes. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem checker_record_parsed_byte_frame (s : MachineState) (source : Nat) (query : Word)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (away : ∀ index, index<34 → query≠s.getReg .x8+BitVec.ofNat 64 index) :
    (checkerRecordParsedState s).getByte query=s.getByte query := by
  have result := native_tail_parse_result (InteriorCodec.recordSpec.map Prod.snd) [] (checkerRecordInput s)
    (checkerRecordParseEntry s) (checker_record_parse_entry_buffer s) (checker_record_input_size s)
    (by intro width member; obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member; exact record_fields_small field belongs)
    (checker_record_parse_entry_widths s)
    (checker_record_parse_entry_input s source (checkerRecordInput s) pointer metadata sourceEnd (checker_record_input_memory s))
    (checker_record_parse_entry_apart s source pointer metadata sourceEnd) (by decide +kernel)
    3 (by decide) (checker_record_parse_entry_end s)
  have rows : (tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] (checkerRecordInput s)).fields.length=17 := by
    rw [tail_parse_plan_length]
    decide +kernel
  rw [checker_record_parsed_eq]
  have same := result.2 query
  change (tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3).getByte query=_ at same
  rw [same,write_parsed_rows_preserves]
  · rw [checker_record_parse_entry_eq]
    change (checkerRecordReadyState s).getByte query=s.getByte query
    exact checker_record_ready_memory s query (fun index inside => away (2*index+1) (by omega))
  · intro index inside
    rw [rows] at inside
    rw [checker_record_parse_entry_metadata]
    exact away (2*index) (by omega)

theorem checker_record_reconstructed_byte_frame (s : MachineState) (source : Nat) (proof : Proof) (query : Word)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (outputAway : ∀ index, index<498 → query≠s.getReg .x6+BitVec.ofNat 64 index)
    (metadataAway : ∀ index, index<34 → query≠s.getReg .x8+BitVec.ofNat 64 index) :
    (checkerRecordReconstructedState s proof).getByte query=s.getByte query := by
  rw [checker_record_reconstructed_eq,inverse_raw_fields_byte_frame]
  · have left : query≠s.getReg .x6+46 := outputAway 46 (by decide)
    have right : query≠s.getReg .x6+47 := outputAway 47 (by decide)
    rw [checker_record_reconstruction_byte,ite_eq_right right,ite_eq_right left]
    exact checker_record_parsed_byte_frame s source query pointer metadata sourceEnd metadataAway
  · intro index inside
    rw [record_raw_fields_length] at inside
    rw [checker_record_reconstruction_output]
    exact outputAway index inside

theorem checker_record_reconstruction_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x5,.x7,.x10,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerRecordReconstructionEntry s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_record_reconstruction_entry_eq,
    checker_record_padding_register _ 4 (by decide) _ (by decide),MachineState.getReg_setPC,
    checker_record_parsed_register _ _ (by decide)]

theorem checker_record_reconstructed_register (s : MachineState) (proof : Proof) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x7,.x9,.x10,.x11,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerRecordReconstructedState s proof).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_record_reconstructed_eq,inverse_raw_fields_register _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    checker_record_reconstruction_register _ _ (by decide)]

end CommitGolfCandidate.Chained.Native

end

section

/-! One complete installed decoder iteration, including both count-control edges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordIterationState (record : InteriorCodec.Record) (s : MachineState) : MachineState :=
  checkerRecordAdvanceState (checkerRecordReconstructedState s (encode record))
def checkerRecordIterationCycles (record : InteriorCodec.Record) (s : MachineState) : Nat :=
  58+checkerRecordParserCycles s+5+2018+checkerRecordAdvanceCycles (checkerRecordReconstructedState s (encode record))

theorem checker_record_iteration_eq (record : InteriorCodec.Record) (s : MachineState) :
    checkerRecordIterationState record s=checkerRecordAdvanceState (checkerRecordReconstructedState s (encode record)) := by
  rw [checkerRecordIterationState]

theorem checker_record_source_payload (record : InteriorCodec.Record) (s : MachineState) (source : Nat)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) (encode record)) :
    checkerRecordParsedPayload (encode record) (checkerRecordInput s)=record := by
  have view : BytesAt s (s.getReg .x18) (encode record) := by rwa [pointer]
  have parsed := checker_record_source_decodes s source (encode record) pointer metadata sourceEnd
    (InteriorCodec.encode_record_length record) view
  exact Option.some.inj (parsed.1.symm.trans (InteriorCodec.record_roundtrip record))

theorem checker_record_iteration_execution (record : InteriorCodec.Record) (s : MachineState) (source outputBase : Nat)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase) (outputEnd : outputBase+498≤checkingMetadataBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) (encode record)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerRecordIterationCycles record s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordIterationState record s) coins
          return result.charge (checkerRecordIterationCycles record s) 0) := by
  have view : BytesAt s (s.getReg .x18) (encode record) := by rwa [pointer]
  rw [checkerRecordIterationCycles,Nat.add_assoc,
    checker_record_initialization_inverse s source outputBase (encode record) pc pointer metadata sourceEnd outputStart
      outputPointer outputEnd (InteriorCodec.encode_record_length record) view,
    checker_record_advance_execution _ (checker_record_reconstructed_pc s source (encode record) pc pointer metadata sourceEnd),
    ←checker_record_iteration_eq]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_record_iteration_bound (record : InteriorCodec.Record) (s : MachineState) :
    checkerRecordIterationCycles record s≤2378 := by
  have bound := checker_record_initialization_inverse_bound s
  unfold checkerRecordIterationCycles checkerRecordAdvanceCycles
  split <;> omega

theorem checker_record_iteration_memory (record : InteriorCodec.Record) (s : MachineState) (source outputBase : Nat)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase) (outputEnd : outputBase+498≤checkingMetadataBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) (encode record)) :
    BytesAt (checkerRecordIterationState record s) (BitVec.ofNat 64 outputBase) (rawFieldsBytes (recordRawFields record)) := by
  have view : BytesAt s (s.getReg .x18) (encode record) := by rwa [pointer]
  have body := (checker_record_reconstructed_content s source outputBase (encode record) pointer metadata sourceEnd outputStart
    outputPointer outputEnd (InteriorCodec.encode_record_length record) view).1
  rw [checker_record_source_payload record s source pointer metadata sourceEnd memory] at body
  intro index inside
  rw [checker_record_iteration_eq,checker_record_advance_byte]
  exact body index inside

theorem checker_record_iteration_source (record : InteriorCodec.Record) (s : MachineState) :
    (checkerRecordIterationState record s).getReg .x18=s.getReg .x18+482 := by
  rw [checker_record_iteration_eq,checker_record_advance_register,checker_record_advance_source,
    checker_record_reconstructed_register _ _ .x18 (by decide)]

theorem checker_record_iteration_counter (record : InteriorCodec.Record) (s : MachineState) (n : Nat)
    (count : s.getReg .x16=BitVec.ofNat 64 (n+1)) :
    (checkerRecordIterationState record s).getReg .x16=BitVec.ofNat 64 n := by
  rw [checker_record_iteration_eq]
  exact checker_record_advance_counter _ n (by rwa [checker_record_reconstructed_register _ _ .x16 (by decide)])

theorem checker_record_iteration_output (record : InteriorCodec.Record) (s : MachineState) (source outputBase : Nat)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase) (outputEnd : outputBase+498≤checkingMetadataBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) (encode record)) :
    (checkerRecordIterationState record s).getReg .x6=BitVec.ofNat 64 (outputBase+498) := by
  rw [checker_record_iteration_eq,checker_record_advance_register,checker_record_advance_prefix_register _ .x6 (by decide)]
  exact (checker_record_reconstructed_content s source outputBase (encode record) pointer metadata sourceEnd outputStart
    outputPointer outputEnd (InteriorCodec.encode_record_length record) (by rwa [pointer])).2.2.1

theorem checker_record_iteration_pc (record : InteriorCodec.Record) (s : MachineState) (source n : Nat)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) (sourceEnd : source+497<checkingRawBase)
    (fit : n<2^64) (count : s.getReg .x16=BitVec.ofNat 64 (n+1)) :
    (checkerRecordIterationState record s).pc=if n=0 then 4096+4*2164 else 4096+4*57 := by
  have done := checker_record_advance_done (checkerRecordReconstructedState s (encode record)) n fit
    (by rwa [checker_record_reconstructed_register _ _ .x16 (by decide)])
  rw [checker_record_iteration_eq,checker_record_advance_pc _
    (checker_record_reconstructed_pc s source (encode record) pc pointer metadata sourceEnd),done]
  simp

theorem checker_record_iteration_byte_frame (record : InteriorCodec.Record) (s : MachineState) (source : Nat) (query : Word)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) (sourceEnd : source+497<checkingRawBase)
    (outputAway : ∀ index, index<498 → query≠s.getReg .x6+BitVec.ofNat 64 index)
    (metadataAway : ∀ index, index<34 → query≠s.getReg .x8+BitVec.ofNat 64 index) :
    (checkerRecordIterationState record s).getByte query=s.getByte query := by
  rw [checker_record_iteration_eq,checker_record_advance_byte]
  exact checker_record_reconstructed_byte_frame s source (encode record) query pointer metadata sourceEnd outputAway metadataAway

theorem checker_record_iteration_register (record : InteriorCodec.Record) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x7,.x9,.x10,.x11,.x16,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerRecordIterationState record s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_record_iteration_eq,checker_record_advance_register,
    checker_record_advance_prefix_register _ _ (by decide),checker_record_reconstructed_register _ _ _ (by decide)]

end CommitGolfCandidate.Chained.Native

end

section

/-! One decoder iteration preserves the encoded suffix and physical loop invariant. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

structure CheckerRecordStreamReady (records : List InteriorCodec.Record) (footer : Proof)
    (s : MachineState) (source outputBase : Nat) : Prop where
  pc : s.pc=if records=[] then 4096+4*2164 else 4096+4*57
  sourcePointer : s.getReg .x18=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase
  metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase
  count : s.getReg .x16=BitVec.ofNat 64 records.length
  countBound : records.length≤LENGTH
  input : BytesAt s (BitVec.ofNat 64 source) (encodedRecords records++footer)
  sourceRange : source+(encodedRecords records++footer).length+512≤checkingRawBase
  outputStart : checkingRawBase≤outputBase
  outputRoom : outputBase+498*records.length+30*256≤checkingMetadataBase

theorem checker_record_stream_head (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source outputBase : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase) :
    BytesAt s (BitVec.ofNat 64 source) (encode record) := by
  have input := ready.input
  change BytesAt s _ ((encode record++encodedRecords records)++footer) at input
  rw [List.append_assoc,bytes_at_append] at input
  exact input.1

theorem checker_record_stream_source_end (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source outputBase : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase) :
    source+497<checkingRawBase := by
  have bound := ready.sourceRange
  rw [List.length_append,encoded_records_length,List.length_cons] at bound
  omega

theorem checker_record_stream_output_end (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source outputBase : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase) :
    outputBase+498≤checkingMetadataBase := by
  have bound := ready.outputRoom
  rw [List.length_cons] at bound
  omega

theorem checker_record_stream_tail (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source outputBase : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase) :
    BytesAt (checkerRecordIterationState record s) (BitVec.ofNat 64 (source+482)) (encodedRecords records++footer) := by
  have input := ready.input
  change BytesAt s _ ((encode record++encodedRecords records)++footer) at input
  rw [List.append_assoc,bytes_at_append] at input
  have tail : BytesAt s (BitVec.ofNat 64 (source+482)) (encodedRecords records++footer) := by
    simpa only [InteriorCodec.encode_record_length,←BitVec.ofNat_add] using input.2
  have sourceEnd := checker_record_stream_source_end record records footer s source outputBase ready
  have outputEnd := checker_record_stream_output_end record records footer s source outputBase ready
  have outputStart := ready.outputStart
  have room := checking_metadata_room
  have range := ready.sourceRange
  rw [List.length_append,encoded_records_length,List.length_cons] at range
  intro index inside
  have bound : index<(encodedRecords records).length+footer.length := by simpa only [List.length_append] using inside
  rw [encoded_records_length] at bound
  rw [checker_record_iteration_byte_frame record s source _ ready.sourcePointer ready.metadata sourceEnd]
  · exact tail index inside
  · intro written before
    rw [ready.outputPointer]
    simp only [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  · intro written before
    rw [ready.metadata]
    simp only [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_record_stream_step (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer : Proof) (s : MachineState) (source outputBase : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase) :
    CheckerRecordStreamReady records footer (checkerRecordIterationState record s) (source+482) (outputBase+498) := by
  have sourceEnd := checker_record_stream_source_end record records footer s source outputBase ready
  have outputEnd := checker_record_stream_output_end record records footer s source outputBase ready
  have head := checker_record_stream_head record records footer s source outputBase ready
  have count : s.getReg .x16=BitVec.ofNat 64 (records.length+1) := ready.count
  have currentPC : s.pc=4096+4*57 := by simpa using ready.pc
  have fit : records.length<2^64 := by
    have size := ready.countBound
    have maximum : LENGTH<2^64 := by decide +kernel
    simp only [List.length_cons] at size
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_eq_zero_iff] using checker_record_iteration_pc record s source records.length
      currentPC ready.sourcePointer ready.metadata sourceEnd fit count
  · rw [checker_record_iteration_source,ready.sourcePointer]
    change BitVec.ofNat 64 source+BitVec.ofNat 64 482=_
    rw [←BitVec.ofNat_add]
  · exact checker_record_iteration_output record s source outputBase ready.sourcePointer ready.metadata sourceEnd ready.outputStart
      ready.outputPointer outputEnd head
  · rw [checker_record_iteration_register _ _ .x8 (by decide)]
    exact ready.metadata
  · exact checker_record_iteration_counter record s records.length count
  · have size := ready.countBound
    simp only [List.length_cons] at size
    omega
  · exact checker_record_stream_tail record records footer s source outputBase ready
  · have bound := ready.sourceRange
    rw [List.length_append,encoded_records_length,List.length_cons] at bound
    rw [List.length_append,encoded_records_length]
    omega
  · have start := ready.outputStart
    omega
  · have bound := ready.outputRoom
    rw [List.length_cons] at bound
    omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Record-count induction for the installed decoder, through footer initialization. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordLoopState : List InteriorCodec.Record → MachineState → MachineState
  | [],s => s
  | record::records,s => checkerRecordLoopState records (checkerRecordIterationState record s)
def checkerRecordLoopCycles : List InteriorCodec.Record → MachineState → Nat
  | [],_ => 0
  | record::records,s => checkerRecordIterationCycles record s+checkerRecordLoopCycles records (checkerRecordIterationState record s)

theorem checker_record_loop_zero (s : MachineState) : checkerRecordLoopState [] s=s := by
  unfold checkerRecordLoopState
  rfl
theorem checker_record_loop_cons (record : InteriorCodec.Record) (records : List InteriorCodec.Record) (s : MachineState) :
    checkerRecordLoopState (record::records) s=checkerRecordLoopState records (checkerRecordIterationState record s) := by
  conv => lhs; unfold checkerRecordLoopState

theorem checker_record_loop_ready (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase) :
    CheckerRecordStreamReady [] footer (checkerRecordLoopState records s)
      (source+482*records.length) (outputBase+498*records.length) := by
  induction records generalizing s source outputBase with
  | nil => simpa only [checker_record_loop_zero,List.length_nil,Nat.mul_zero,Nat.add_zero] using ready
  | cons record records ih =>
    have next := checker_record_stream_step record records footer s source outputBase ready
    have result := ih _ _ _ next
    have src : source+482+482*records.length=source+482*(record::records).length := by simp only [List.length_cons]; omega
    have dst : outputBase+498+498*records.length=outputBase+498*(record::records).length := by simp only [List.length_cons]; omega
    rw [src,dst] at result
    rw [checker_record_loop_cons]
    exact result

theorem checker_record_loop_execution (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerRecordLoopCycles records s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordLoopState records s) coins
          return result.charge (checkerRecordLoopCycles records s) 0) := by
  induction records generalizing s source outputBase with
  | nil => simp [checkerRecordLoopCycles,checker_record_loop_zero,Execution.charge]
  | cons record records ih =>
    have next := checker_record_stream_step record records footer s source outputBase ready
    have rest := ih _ _ _ next
    rw [checkerRecordLoopCycles,Nat.add_assoc,
      checker_record_iteration_execution record s source outputBase (by simpa using ready.pc)
        ready.sourcePointer ready.metadata (checker_record_stream_source_end record records footer s source outputBase ready)
        ready.outputStart ready.outputPointer (checker_record_stream_output_end record records footer s source outputBase ready)
        (checker_record_stream_head record records footer s source outputBase ready),
      rest,checker_record_loop_cons]
    simp [Execution.charge,Nat.add_assoc]

theorem checker_record_loop_bound (records : List InteriorCodec.Record) (s : MachineState) :
    checkerRecordLoopCycles records s≤2378*records.length := by
  induction records generalizing s with
  | nil => simp [checkerRecordLoopCycles]
  | cons record records ih =>
    have head := checker_record_iteration_bound record s
    have rest := ih (checkerRecordIterationState record s)
    simp only [checkerRecordLoopCycles,List.length_cons,Nat.mul_add]
    omega

theorem checker_record_iteration_prefix (record : InteriorCodec.Record) (records : List InteriorCodec.Record)
    (footer past : Proof) (s : MachineState) (source outputBase base : Nat)
    (ready : CheckerRecordStreamReady (record::records) footer s source outputBase)
    (previous : BytesAt s (BitVec.ofNat 64 base) past) (endpoint : base+past.length=outputBase) :
    BytesAt (checkerRecordIterationState record s) (BitVec.ofNat 64 base) (past++rawFieldsBytes (recordRawFields record)) := by
  have sourceEnd := checker_record_stream_source_end record records footer s source outputBase ready
  have outputEnd := checker_record_stream_output_end record records footer s source outputBase ready
  have room := checking_metadata_room
  rw [bytes_at_append]
  refine ⟨?_,?_⟩
  · intro index inside
    rw [checker_record_iteration_byte_frame record s source _ ready.sourcePointer ready.metadata sourceEnd]
    · exact previous index inside
    · intro written before
      rw [ready.outputPointer]
      simp only [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
    · intro written before
      rw [ready.metadata]
      simp only [←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  · rw [←BitVec.ofNat_add,endpoint]
    exact checker_record_iteration_memory record s source outputBase ready.sourcePointer ready.metadata sourceEnd ready.outputStart
      ready.outputPointer outputEnd (checker_record_stream_head record records footer s source outputBase ready)

theorem checker_record_loop_prefix (records : List InteriorCodec.Record) (footer past : Proof) (s : MachineState)
    (source outputBase base : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase)
    (previous : BytesAt s (BitVec.ofNat 64 base) past) (endpoint : base+past.length=outputBase) :
    BytesAt (checkerRecordLoopState records s) (BitVec.ofNat 64 base) (past++rawRecordStream records) := by
  induction records generalizing s source outputBase past with
  | nil => simpa only [checker_record_loop_zero,rawRecordStream,List.flatMap_nil,List.append_nil] using previous
  | cons record records ih =>
    have next := checker_record_stream_step record records footer s source outputBase ready
    have written := checker_record_iteration_prefix record records footer past s source outputBase base ready previous endpoint
    have endNext : base+(past++rawFieldsBytes (recordRawFields record)).length=outputBase+498 := by
      rw [List.length_append,record_raw_fields_length]
      omega
    have result := ih (past++rawFieldsBytes (recordRawFields record)) _ _ _ next written endNext
    simpa only [checker_record_loop_cons,rawRecordStream,List.flatMap_cons,List.append_assoc] using result

theorem checker_record_loop_memory (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (ready : CheckerRecordStreamReady records footer s source outputBase) :
    BytesAt (checkerRecordLoopState records s) (BitVec.ofNat 64 outputBase) (rawRecordStream records) := by
  have empty : BytesAt s (BitVec.ofNat 64 outputBase) [] := by intro index inside; simp at inside
  simpa only [List.nil_append] using checker_record_loop_prefix records footer [] s source outputBase outputBase ready empty (by simp)

theorem checker_record_loop_register (records : List InteriorCodec.Record) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x5,.x6,.x7,.x9,.x10,.x11,.x16,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerRecordLoopState records s).getReg reg=s.getReg reg := by
  induction records generalizing s with
  | nil => rw [checker_record_loop_zero]
  | cons record records ih => rw [checker_record_loop_cons,ih,checker_record_iteration_register _ _ reg kept]

theorem checker_record_loop_byte_frame (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source outputBase : Nat) (query : Word) (ready : CheckerRecordStreamReady records footer s source outputBase)
    (outputAway : ∀ index, index<498*records.length → query≠BitVec.ofNat 64 outputBase+BitVec.ofNat 64 index)
    (metadataAway : ∀ index, index<34 → query≠BitVec.ofNat 64 checkingMetadataBase+BitVec.ofNat 64 index) :
    (checkerRecordLoopState records s).getByte query=s.getByte query := by
  induction records generalizing s source outputBase with
  | nil => rw [checker_record_loop_zero]
  | cons record records ih =>
    have next := checker_record_stream_step record records footer s source outputBase ready
    have restAway : ∀ index, index<498*records.length →
        query≠BitVec.ofNat 64 (outputBase+498)+BitVec.ofNat 64 index := by
      intro index inside
      have original := outputAway (498+index) (by simp only [List.length_cons]; omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using original
    have rest := ih _ _ _ next restAway
    rw [checker_record_loop_cons,rest]
    apply checker_record_iteration_byte_frame record s source query ready.sourcePointer ready.metadata
      (checker_record_stream_source_end record records footer s source outputBase ready)
    · intro index inside
      rw [ready.outputPointer]
      exact outputAway index (by simp only [List.length_cons]; omega)
    · intro index inside
      rw [ready.metadata]
      exact metadataAway index inside

end CommitGolfCandidate.Chained.Native

end

section

/-! Arbitrary supplied record bytes instantiate the typed decoder-loop invariant. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem checker_record_decode_total (proof : Proof) (length : proof.length=482) :
    encode (decode InteriorCodec.recordSpec proof)=proof := by
  let input : Nat → List Bool := fun index => byteBits ((proof.drop 479).getD index 0)
  have byteSize : ∀ index, (input index).length=8 := fun _ => byte_bits_length _
  have plan := checker_record_plan_complete input byteSize
  have canonical : encode (checkerRecordParsedPayload proof input)=proof := by
    apply inverse_canonical InteriorCodec.recordSpec proof input (by decide +kernel) record_fields_small
      (by rw [InteriorCodec.record_counts.1,length]; decide) byteSize
    · intro index inside
      rfl
    · simpa only [InteriorCodec.record_counts.1,List.length_drop,length] using plan.1
    · rw [plan.2]
      intro index inside
      simp at inside
  conv_lhs => rw [←canonical,decode_encode]
  exact canonical

def checkerDecodeRecords : Nat → Proof → List InteriorCodec.Record
  | 0,_ => []
  | n+1,proof => decode InteriorCodec.recordSpec (proof.take 482)::checkerDecodeRecords n (proof.drop 482)

theorem checker_decode_records_length (n : Nat) (proof : Proof) : (checkerDecodeRecords n proof).length=n := by
  induction n generalizing proof with
  | zero => rfl
  | succ n ih => simp only [checkerDecodeRecords,List.length_cons,ih]

theorem checker_decode_records_encoded (n : Nat) (proof : Proof) (enough : 482*n≤proof.length) :
    encodedRecords (checkerDecodeRecords n proof)=proof.take (482*n) := by
  induction n generalizing proof with
  | zero => simp [checkerDecodeRecords,encodedRecords]
  | succ n ih =>
    have head : (proof.take 482).length=482 := by
      rw [List.length_take,Nat.min_eq_left (by omega)]
    have tail : 482*n≤(proof.drop 482).length := by rw [List.length_drop]; omega
    change encode (decode InteriorCodec.recordSpec (proof.take 482))++
      encodedRecords (checkerDecodeRecords n (proof.drop 482))=_
    rw [checker_record_decode_total _ head,ih _ tail,
      show 482*(n+1)=482+482*n by omega,List.take_add]

theorem checker_decode_records_partition (n : Nat) (proof : Proof) (enough : 482*n≤proof.length) :
    encodedRecords (checkerDecodeRecords n proof)++proof.drop (482*n)=proof := by
  rw [checker_decode_records_encoded n proof enough,List.take_append_drop]

theorem checker_record_untrusted_ready (n : Nat) (proof : Proof) (s : MachineState) (source outputBase : Nat)
    (enough : 482*n≤proof.length) (countBound : n≤LENGTH)
    (pc : s.pc=if n=0 then 4096+4*2164 else 4096+4*57)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (counter : s.getReg .x16=BitVec.ofNat 64 n)
    (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (sourceRange : source+proof.length+512≤checkingRawBase)
    (outputStart : checkingRawBase≤outputBase)
    (outputRoom : outputBase+498*n+30*256≤checkingMetadataBase) :
    CheckerRecordStreamReady (checkerDecodeRecords n proof) (proof.drop (482*n)) s source outputBase := by
  have empty : checkerDecodeRecords n proof=[] ↔ n=0 := by
    rw [←List.length_eq_zero_iff,checker_decode_records_length]
  refine ⟨?_,pointer,outputPointer,metadata,?_,?_,?_,?_,outputStart,?_⟩
  · simpa only [empty] using pc
  · rwa [checker_decode_records_length]
  · rwa [checker_decode_records_length]
  · rwa [checker_decode_records_partition n proof enough]
  · rwa [checker_decode_records_partition n proof enough]
  · rwa [checker_decode_records_length]

end CommitGolfCandidate.Chained.Native

end
