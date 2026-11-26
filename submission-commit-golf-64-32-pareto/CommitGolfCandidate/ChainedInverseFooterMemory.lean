import CommitGolfCandidate.ChainedInverseFooterRun

/-! Projected memory refinement for the variable-count inverse footer. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem low_copy_bytes_congr (n : Nat) (before after : MachineState)
    (memory : ∀ query, after.getByte query=before.getByte query)
    (source : after.getReg .x5=before.getReg .x5)
    (output : after.getReg .x6=before.getReg .x6) (query : Word) :
    (lowCopyState n after).getByte query=(lowCopyState n before).getByte query := by
  induction n generalizing before after with
  | zero => simpa only [low_copy_zero] using memory query
  | succ n ih =>
    rw [low_copy_succ,low_copy_succ]
    apply ih
    · intro address
      simp only [byte_copy_byte,source,output,memory]
    · rw [byte_copy_source,byte_copy_source,source]
    · rw [byte_copy_destination,byte_copy_destination,output]

theorem inverse_field_bytes_congr (n : Nat) (before after : MachineState)
    (memory : ∀ query, after.getByte query=before.getByte query)
    (source : after.getReg .x5=before.getReg .x5)
    (output : after.getReg .x6=before.getReg .x6)
    (metadata : after.getReg .x7=before.getReg .x7) (query : Word) :
    (inverseFieldState n after).getByte query=(inverseFieldState n before).getByte query := by
  simp only [inverseFieldState,inverse_field_tail_byte,low_copy_destination,
    low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),output,metadata,
    low_copy_bytes_congr n before after memory source output]

theorem inverse_footer_raw_byte (field : RawField) (s : MachineState)
    (low : field.low.length=29) (query : Word) :
    (inverseFooterFieldState s).getByte query=(field.inverseState s).getByte query := by
  rw [inverse_footer_field_byte,RawField.inverseState,low]
  apply inverse_field_bytes_congr
  · intro address
    rw [field_header_byte]
  · rw [field_header_frame _ _ _ .x5 (by decide) (by decide)]
  · rw [field_header_frame _ _ _ .x6 (by decide) (by decide)]
  · rw [field_header_frame _ _ _ .x7 (by decide) (by decide)]

theorem inverse_fields_ready_congr (fields : List RawField) (suffix completed : Proof)
    (before after : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady fields suffix completed before source outputBase metadata)
    (memory : ∀ query, after.getByte query=before.getByte query)
    (inputReg : after.getReg .x5=before.getReg .x5)
    (outputReg : after.getReg .x6=before.getReg .x6)
    (metaReg : after.getReg .x7=before.getReg .x7) :
    InverseFieldsReady fields suffix completed after source outputBase metadata := by
  refine ⟨inputReg.trans ready.sourcePointer,outputReg.trans ready.outputPointer,
    metaReg.trans ready.metaPointer,?_,?_,?_,?_,ready.inputBefore,ready.outputBefore,ready.room⟩
  · intro index inside; rw [memory]; exact ready.input index inside
  · intro index inside; rw [memory]; exact ready.output index inside
  · intro index inside; rw [memory]; exact ready.table index inside
  · exact raw_padding_frame before after _ fields ready.padding (fun index _ => memory _)

theorem inverse_footer_memory_step (field : RawField) (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady (field::fields) suffix completed s source outputBase metadata)
    (low : field.low.length=29) (padding : field.padding=[]) (skip : s.getReg .x9=1#64) :
    InverseFieldsReady fields suffix (completed++field.bytes) (inverseFooterFieldState s)
      (source+field.low.length) outputBase (metadata+2) := by
  have next := inverse_fields_step field fields suffix completed s source outputBase metadata ready
  apply inverse_fields_ready_congr _ _ _ _ _ _ _ _ next (inverse_footer_raw_byte field s low)
  · rw [inverse_footer_field_register _ .x5 (by decide),inverse_field_source,inverse_raw_field_source,low]
  · rw [inverse_footer_field_register _ .x6 (by decide),inverse_field_destination,
      inverse_raw_field_destination,skip]
    have length : field.bytes.length=30 := by simp [RawField.bytes,low,padding]
    rw [length]
    change (s.getReg .x6+29#64)+1#64=s.getReg .x6+30#64
    rw [BitVec.add_assoc]
    rfl
  · rw [inverse_footer_field_register _ .x7 (by decide),inverse_field_descriptor,inverse_raw_field_descriptor]

theorem inverse_footer_rows_memory (fields : List RawField) (suffix completed : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady fields suffix completed s source outputBase metadata)
    (lows : ∀ field ∈ fields, field.low.length=29)
    (padding : ∀ field ∈ fields, field.padding=[])
    (skip : s.getReg .x9=1#64) :
    InverseFieldsReady [] suffix (completed++rawFieldsBytes fields)
      (inverseFooterRowsState fields.length s) (source+(rawFieldsLow fields).length)
      outputBase (metadata+2*fields.length) := by
  induction fields generalizing s source metadata completed with
  | nil =>
    simpa only [List.length_nil,inverse_footer_rows_zero,rawFieldsLow,rawFieldsBytes,
      List.flatMap_nil,List.append_nil,List.length_nil,Nat.add_zero,Nat.mul_zero] using ready
  | cons field fields ih =>
    have next := inverse_footer_memory_step field fields suffix completed s source outputBase metadata
      ready (lows field (by simp)) (padding field (by simp)) skip
    have nextSkip : (inverseFooterFieldState s).getReg .x9=1#64 := by
      rw [inverse_footer_field_register _ .x9 (by decide),
        inverse_field_frame _ _ .x9 (by decide) (by decide) (by decide) (by decide)]
      exact skip
    have result := ih (completed++field.bytes) (inverseFooterFieldState s) (source+field.low.length)
      (metadata+2) next (fun row member => lows row (by simp [member]))
        (fun row member => padding row (by simp [member])) nextSkip
    simpa only [List.length_cons,inverse_footer_rows_succ,rawFieldsLow,rawFieldsBytes,
      List.flatMap_cons,List.length_append,List.append_assoc,Nat.mul_add,Nat.mul_one,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

end CommitGolfCandidate.Chained.Native
