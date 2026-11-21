import CommitGolfCandidate.ChainedRecordWidths

/-! Trusted width writes preserve parser input and feed strict record acceptance. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

theorem width_table_parse_buffer (widths : List (Fin 7)) (s : MachineState) (front : List Bool)
    (buffer : TailParseBuffer s front) : TailParseBuffer (widthTableState widths s) front := by
  constructor
  · rw [width_table_register widths s .x23 (by decide) (by decide)]
    exact buffer.value
  · rw [width_table_register widths s .x25 (by decide) (by decide)]
    exact buffer.count
  · exact buffer.pending

theorem width_table_parse_input (widths : List (Fin 7)) (s : MachineState)
    (input : Nat → List Bool) (count : Nat) (memory : ParseInputAt s (s.getReg .x20) input count)
    (away : ∀ index, index≤count → ∀ row, row<widths.length →
      s.getReg .x20+BitVec.ofNat 64 index≠s.getReg .x7+BitVec.ofNat 64 (2*row+1)) :
    ParseInputAt (widthTableState widths s) ((widthTableState widths s).getReg .x20) input count := by
  intro index inside
  rw [width_table_register widths s .x20 (by decide) (by decide),
    width_table_byte_frame widths s _ (away index inside)]
  exact memory index inside

theorem initialized_record_parser_accepts (s : MachineState) (proof : Proof) (input : Nat → List Bool)
    (metadata : s.getReg .x21=s.getReg .x7) (buffer : TailParseBuffer s [])
    (byteSize : ∀ index, (input index).length=8) (enough : 479≤proof.length)
    (memory : ParseInputAt s (s.getReg .x20) input 17)
    (away : ∀ index, index≤17 → ∀ row, row<17 →
      s.getReg .x20+BitVec.ofNat 64 index≠s.getReg .x7+BitVec.ofNat 64 (2*row+1))
    (apart : TailApart (s.getReg .x21) (s.getReg .x20)
      ((InteriorCodec.recordSpec.map Prod.snd).map fun _ => []))
    (endFit : (proof.drop 479).length<2^64)
    (endPointer : s.getReg .x19=s.getReg .x20+BitVec.ofNat 64 (proof.drop 479).length)
    (source : ∀ index, index<(proof.drop 479).length →
      input index=byteBits ((proof.drop 479).getD index 0)) :
    (tailValidatePrefix (tailParsedFieldsState 17 (widthTableState recordWidths s)) 3).getReg .x24=1#64 →
      ∃ record : InteriorCodec.Record, unpack InteriorCodec.recordSpec proof=some record ∧ proof.length=482 := by
  let initialized := widthTableState recordWidths s
  have table : ParseWidthsAt initialized (initialized.getReg .x21) (InteriorCodec.recordSpec.map Prod.snd) := by
    rw [width_table_register recordWidths s .x21 (by decide) (by decide),metadata]
    exact native_record_widths s
  have initializedMemory : ParseInputAt initialized (initialized.getReg .x20) input 17 := by
    apply width_table_parse_input recordWidths s input 17 memory
    simpa only [record_widths_count] using away
  have initializedApart : TailApart (initialized.getReg .x21) (initialized.getReg .x20)
      ((InteriorCodec.recordSpec.map Prod.snd).map fun _ => []) := by
    simpa only [initialized,width_table_register recordWidths s .x21 (by decide) (by decide),
      width_table_register recordWidths s .x20 (by decide) (by decide)] using apart
  have initializedEnd : initialized.getReg .x19=initialized.getReg .x20+BitVec.ofNat 64 (proof.drop 479).length := by
    simpa only [initialized,width_table_register recordWidths s .x19 (by decide) (by decide),
      width_table_register recordWidths s .x20 (by decide) (by decide)] using endPointer
  have result := parsed_payload_accepts InteriorCodec.recordSpec proof input initialized
    (width_table_parse_buffer recordWidths s [] buffer) byteSize (by decide +kernel) record_fields_small
    (by simpa only [InteriorCodec.record_counts.1] using enough) table initializedMemory initializedApart
    (by decide +kernel) (by simpa only [InteriorCodec.record_counts.1] using endFit)
    (by simpa only [InteriorCodec.record_counts.1] using initializedEnd)
    (by simpa only [InteriorCodec.record_counts.1] using source)
  intro accepted
  have parsed := result accepted
  refine ⟨_,parsed.1,?_⟩
  have length := congrArg List.length (accepted_encode proof _ parsed.1)
  rw [InteriorCodec.encode_record_length] at length
  exact length.symm

end CommitGolfCandidate.Chained.Native
