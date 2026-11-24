import CommitGolfCandidate.ChainedRecordPrefix

/-! Whole record-count induction for the actual forward controller, before its footer. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def recordLoopState : List InteriorCodec.Record → MachineState → MachineState
  | [],s => s
  | record::records,s => recordLoopState records (recordIterationState record s)
def recordLoopCycles : List InteriorCodec.Record → MachineState → Nat
  | [],_ => 0
  | record::records,s => recordIterationCycles record s+recordLoopCycles records (recordIterationState record s)
def encodedRecords (records : List InteriorCodec.Record) : Proof := records.flatMap encode

theorem record_loop_zero (s : MachineState) : recordLoopState [] s=s := by unfold recordLoopState; rfl
theorem record_loop_cons (record : InteriorCodec.Record) (records : List InteriorCodec.Record) (s : MachineState) :
    recordLoopState (record::records) s=recordLoopState records (recordIterationState record s) := by
  conv => lhs; unfold recordLoopState

theorem encoded_records_length (records : List InteriorCodec.Record) :
    (encodedRecords records).length=482*records.length := by
  induction records with
  | nil => rfl
  | cons record records ih =>
    change (encode record++encodedRecords records).length=_
    rw [List.length_append,InteriorCodec.encode_record_length,ih,List.length_cons,Nat.mul_add]
    omega

theorem record_loop_ready (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source output metadata : Nat) (ready : RecordStreamReady records footer s source output metadata) :
    RecordStreamReady [] footer (recordLoopState records s)
      (source+498*records.length) (output+482*records.length) metadata := by
  induction records generalizing s source output with
  | nil => simpa only [record_loop_zero,List.length_nil,Nat.mul_zero,Nat.add_zero] using ready
  | cons record records ih =>
    have next := record_stream_step record records footer s source output metadata ready
    have result := ih _ _ _ next
    have src : source+498+498*records.length=source+498*(record::records).length := by simp only [List.length_cons]; omega
    have dst : output+482+482*records.length=output+482*(record::records).length := by simp only [List.length_cons]; omega
    rw [src,dst] at result
    rw [record_loop_cons]
    exact result

theorem record_loop_execution (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source output metadata : Nat) (ready : RecordStreamReady records footer s source output metadata)
    (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (recordLoopCycles records s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordLoopState records s) coins
          return result.charge (recordLoopCycles records s) 0) := by
  induction records generalizing s source output with
  | nil => simp [recordLoopCycles,record_loop_zero,Execution.charge]
  | cons record records ih =>
    have next := record_stream_step record records footer s source output metadata ready
    have rest := ih _ _ _ next
    have raw : BytesAt s (BitVec.ofNat 64 source)
        (rawFieldsBytes (recordRawFields record)++(rawRecordStream records++footer)) := by
      simpa only [rawRecordStream,List.flatMap_cons,List.append_assoc] using ready.memory
    have separate : source+498+(rawRecordStream records++footer).length≤metadata := by
      have bound := ready.separate
      rw [List.length_append,raw_record_stream_length]
      simp only [List.length_cons,Nat.mul_add] at bound
      omega
    rw [recordLoopCycles,Nat.add_assoc,
      record_iteration_execution record _ s source output metadata (by simpa using ready.pc)
        ready.sourcePointer ready.outputPointer ready.scratch raw ready.ordered separate ready.capacity,
      rest,record_loop_cons]
    simp [recordLoopCycles,Execution.charge,Nat.add_assoc]

theorem record_loop_bound (records : List InteriorCodec.Record) (s : MachineState) :
    recordLoopCycles records s≤2273*records.length := by
  induction records generalizing s with
  | nil => simp [recordLoopCycles]
  | cons record records ih =>
    have head := record_iteration_bound record s
    have rest := ih (recordIterationState record s)
    simp only [recordLoopCycles,List.length_cons,Nat.mul_add]
    omega

theorem record_loop_prefix (records : List InteriorCodec.Record) (footer past : Proof) (s : MachineState)
    (source output metadata base : Nat) (ready : RecordStreamReady records footer s source output metadata)
    (previous : BytesAt s (BitVec.ofNat 64 base) past) (endpoint : base+past.length=output) :
    BytesAt (recordLoopState records s) (BitVec.ofNat 64 base) (past++encodedRecords records) := by
  induction records generalizing s source output past with
  | nil => simpa only [record_loop_zero,encodedRecords,List.flatMap_nil,List.append_nil] using previous
  | cons record records ih =>
    have next := record_stream_step record records footer s source output metadata ready
    have written := record_iteration_prefix record records footer past s source output metadata base ready previous endpoint
    have endNext : base+(past++encode record).length=output+482 := by
      rw [List.length_append,InteriorCodec.encode_record_length]
      omega
    have result := ih (past++encode record) _ _ _ next written endNext
    simpa only [record_loop_cons,encodedRecords,List.flatMap_cons,List.append_assoc] using result

theorem record_loop_memory (records : List InteriorCodec.Record) (footer : Proof) (s : MachineState)
    (source output metadata : Nat) (ready : RecordStreamReady records footer s source output metadata) :
    BytesAt (recordLoopState records s) (BitVec.ofNat 64 output) (encodedRecords records) := by
  have empty : BytesAt s (BitVec.ofNat 64 output) [] := by intro index inside; simp at inside
  simpa only [List.nil_append] using record_loop_prefix records footer [] s source output metadata output ready empty (by simp)

theorem record_loop_range_execution (records : List InteriorCodec.Record) (s : MachineState)
    (source output metadata : Nat) (pc : s.pc=if records=[] then 12380 else 4120)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (count : s.getReg .x29=BitVec.ofNat 64 records.length)
    (ordered : output≤source) (sourceRoom : source+498*records.length≤MEMORY_BYTES)
    (metaRoom : metadata+34≤MEMORY_BYTES) :
    (∀ fuel coins, execute openingControllerImage (recordLoopCycles records s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordLoopState records s) coins
          return result.charge (recordLoopCycles records s) 0)) ∧
    (recordLoopState records s).pc=12380 ∧
    (recordLoopState records s).getReg .x5=BitVec.ofNat 64 (source+498*records.length) ∧
    ∃ increment : Nat, increment≤497*records.length ∧
      (recordLoopState records s).getReg .x6=BitVec.ofNat 64 (output+increment) := by
  induction records generalizing s source output with
  | nil =>
    refine ⟨?_,?_,?_,0,by simp,?_⟩
    · intro fuel coins
      simp [recordLoopCycles,record_loop_zero,Execution.charge]
    · simpa only [record_loop_zero,ite_true] using pc
    · simpa only [record_loop_zero,List.length_nil,Nat.mul_zero,Nat.add_zero] using sourcePointer
    · simpa only [record_loop_zero,Nat.add_zero] using outputPointer
  | cons record records ih =>
    have start : s.pc=4120 := by simpa using pc
    have firstCount : s.getReg .x29=BitVec.ofNat 64 (records.length+1) := by
      simpa only [List.length_cons] using count
    have room : source+498+498*records.length≤MEMORY_BYTES := by
      simp only [List.length_cons] at sourceRoom
      omega
    have fit : records.length<2^64 := by unfold MEMORY_BYTES at room; omega
    obtain ⟨firstRun,firstPC,firstSource,firstCounter,step,stepBound,firstOutput⟩ :=
      record_iteration_range_execution record s source output metadata records.length start
        sourcePointer outputPointer scratch firstCount fit (by omega) (by omega) metaRoom
    have nextPC : (recordIterationState record s).pc=if records=[] then 12380 else 4120 := by
      cases records <;> simpa using firstPC
    have nextScratch : (recordIterationState record s).getReg .x17+0x200000000=
        BitVec.ofNat 64 metadata := by
      rw [recordIterationState,record_post_register,
        record_post_prefix_register _ .x17 (by decide) (by decide),
        record_pack_control _ _ .x17 (by simp),record_reset_register _ .x17 (by decide)]
      exact scratch
    obtain ⟨restRun,restPC,restSource,increment,incrementBound,restOutput⟩ :=
      ih (recordIterationState record s) (source+498) (output+step) nextPC firstSource
        firstOutput nextScratch firstCounter (by omega) room
    refine ⟨?_,?_,?_,step+increment,?_,?_⟩
    · intro fuel coins
      rw [recordLoopCycles,Nat.add_assoc,firstRun,restRun,record_loop_cons]
      simp [recordLoopCycles,Execution.charge,Nat.add_assoc]
    · simpa only [record_loop_cons] using restPC
    · have advance : source+498+498*records.length=source+498*(record::records).length := by
        simp only [List.length_cons]
        omega
      simpa only [record_loop_cons,advance] using restSource
    · simp only [List.length_cons]
      omega
    · simpa only [record_loop_cons,Nat.add_assoc] using restOutput

end CommitGolfCandidate.Chained.Native
