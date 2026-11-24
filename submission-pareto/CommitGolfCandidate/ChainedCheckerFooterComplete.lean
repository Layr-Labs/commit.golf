import CommitGolfCandidate.ChainedCheckerFooterSetup
import CommitGolfCandidate.ChainedInverseFooterPayload

section

/-! Empty/nonempty installed parser entry and physical variable-row readiness. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerFooterParseEntry (s : MachineState) : MachineState :=
  (checkerFooterParseSetupState s).setPC ((checkerFooterParseSetupState s).pc+
    if (checkerFooterParseSetupState s).getReg .x22==0#64 then 72 else 4)
theorem checker_footer_parse_entry_eq (s : MachineState) : checkerFooterParseEntry s=
    (checkerFooterParseSetupState s).setPC ((checkerFooterParseSetupState s).pc+
      if (checkerFooterParseSetupState s).getReg .x22==0#64 then 72 else 4) := by
  rw [checkerFooterParseEntry]

private theorem merged_ChainedCheckerFooterParseState_entry_branch_eq (s : MachineState) : execInstrBr s (.BEQ .x22 .x0 72)=
    s.setPC (s.pc+if s.getReg .x22==0#64 then 72 else 4) := by
  change (if s.getReg .x22==0#64 then s.setPC (s.pc+signExtend13 72) else s.setPC (s.pc+4))=_
  by_cases empty : s.getReg .x22==0#64 <;> simp only [empty,↓reduceIte] <;> rfl

theorem checker_footer_parse_entry_register (s : MachineState) (reg : Reg) :
    (checkerFooterParseEntry s).getReg reg=(checkerFooterParseSetupState s).getReg reg := by
  rw [checker_footer_parse_entry_eq,MachineState.getReg_setPC]
theorem checker_footer_parse_entry_memory (s : MachineState) (query : Word) :
    (checkerFooterParseEntry s).getMem query=s.getMem query := by
  rw [checker_footer_parse_entry_eq,MachineState.getMem_setPC,checker_footer_parse_setup_memory]
theorem checker_footer_parse_entry_byte (s : MachineState) (query : Word) :
    (checkerFooterParseEntry s).getByte query=s.getByte query := by
  simp only [MachineState.getByte,checker_footer_parse_entry_memory]
theorem checker_footer_parse_entry_metadata (s : MachineState) :
    (checkerFooterParseEntry s).getReg .x21=s.getReg .x8 := by
  rw [checker_footer_parse_entry_register,checker_footer_parse_setup_metadata]
theorem checker_footer_parse_entry_count (s : MachineState) :
    (checkerFooterParseEntry s).getReg .x22=s.getReg .x22 := by
  rw [checker_footer_parse_entry_register,checker_footer_parse_setup_count]
theorem checker_footer_parse_entry_source (s : MachineState) (source count : Nat) (bounded : count≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 count) :
    (checkerFooterParseEntry s).getReg .x20=BitVec.ofNat 64 (source+29*count) := by
  rw [checker_footer_parse_entry_register,checker_footer_parse_setup_source s source count bounded pointer rows]
theorem checker_footer_parse_entry_buffer (s : MachineState) : TailParseBuffer (checkerFooterParseEntry s) [] := by
  have buffer := checker_footer_parse_setup_buffer s
  refine ⟨?_,?_,buffer.pending⟩
  · rw [checker_footer_parse_entry_register]; exact buffer.value
  · rw [checker_footer_parse_entry_register]; exact buffer.count
theorem checker_footer_parse_entry_widths (s : MachineState) (widths : List Nat)
    (table : ParseWidthsAt s (s.getReg .x8) widths) :
    ParseWidthsAt (checkerFooterParseEntry s) ((checkerFooterParseEntry s).getReg .x21) widths := by
  intro index inside
  rw [checker_footer_parse_entry_metadata,checker_footer_parse_entry_byte]
  exact table index inside

theorem checker_footer_parse_entry_pc (s : MachineState) (count : Nat) (bounded : count≤256)
    (rows : s.getReg .x22=BitVec.ofNat 64 count) (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s) :
    (checkerFooterParseEntry s).pc=if count=0 then (4096+4*2202)+72 else (4096+4*2202)+4 := by
  rw [checker_footer_parse_entry_eq]
  change (checkerFooterParseSetupState s).pc+(if (checkerFooterParseSetupState s).getReg .x22==0#64 then 72 else 4)=_
  rw [checker_footer_parse_setup_pc s pc enough,checker_footer_parse_setup_count,rows]
  by_cases empty : count=0
  · subst count; rfl
  · have nonzero : BitVec.ofNat 64 count≠0#64 := by
      intro same
      have natural := congrArg BitVec.toNat same
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at natural
      exact empty natural
    simp [nonzero,empty]

theorem checker_footer_parser_enter (s : MachineState) (pc : s.pc=4096+4*2190)
    (enough : CheckerFooterLowBodyFits s) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) (checkerFooterParseSetupState s) coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterParseEntry s) coins
          return result.charge 1 0) := by
  have fetched : fetch chainedCheckerImage (checkerFooterParseSetupState s)=some (.base (.BEQ .x22 .x0 72)) :=
    chained_checker_footer_parse_at ⟨0,by decide⟩ _ (by simpa using checker_footer_parse_setup_pc s pc enough)
  have ordinary : ordinaryStep (checkerFooterParseSetupState s) (.base (.BEQ .x22 .x0 72))=some (checkerFooterParseEntry s) := by
    change some (execInstrBr _ (.BEQ .x22 .x0 72))=_
    rw [merged_ChainedCheckerFooterParseState_entry_branch_eq,checker_footer_parse_entry_eq]
  simpa only [Nat.add_comm,instructionCycles] using
    execute_ordinary_step chainedCheckerImage _ _ _ fuel coins fetched ordinary

def checkerFooterInput (s : MachineState) (source count index : Nat) : List Bool :=
  byteBits (s.getByte (BitVec.ofNat 64 (source+29*count)+BitVec.ofNat 64 index))
theorem checker_footer_input_size (s : MachineState) (source count index : Nat) :
    (checkerFooterInput s source count index).length=8 := byte_bits_length _
theorem checker_footer_parse_entry_input (s : MachineState) (source count : Nat) (bounded : count≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 count) :
    ParseInputAt (checkerFooterParseEntry s) ((checkerFooterParseEntry s).getReg .x20)
      (checkerFooterInput s source count) count := by
  intro index inside
  rw [checker_footer_parse_entry_source s source count bounded pointer rows,checker_footer_parse_entry_byte]
  exact (byte_bits_word _).symm

theorem checker_footer_parse_entry_apart (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase) :
    TailApart ((checkerFooterParseEntry s).getReg .x21) ((checkerFooterParseEntry s).getReg .x20)
      (widths.map fun _ => []) := by
  rw [checker_footer_parse_entry_metadata,metadata,checker_footer_parse_entry_source s source widths.length bounded pointer rows]
  apply tail_apart_of_ranges
  · have order : checkingRawBase<checkingMetadataBase := by decide +kernel
    simp only [List.length_map]
    omega
  · have room : checkingMetadataBase+512≤MEMORY_BYTES := by decide +kernel
    simp only [List.length_map]
    omega

theorem checker_footer_parser_ready (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths) :
    TailParsedFieldsReady widths.length (checkerFooterParseEntry s) := by
  have sourceRoom : checkingMetadataBase+2*widths.length≤MEMORY_BYTES := by
    have room : checkingMetadataBase+512≤MEMORY_BYTES := by decide +kernel
    omega
  have inputRoom : source+29*widths.length+widths.length+1≤MEMORY_BYTES := by
    have rawRoom : checkingRawBase≤MEMORY_BYTES := by decide +kernel
    omega
  exact tail_parsed_rows_access widths [] (checkerFooterInput s source widths.length) (checkerFooterParseEntry s)
    checkingMetadataBase (source+29*widths.length) (checker_footer_parse_entry_buffer s)
    (checker_footer_input_size s source widths.length) small (checker_footer_parse_entry_widths s widths table)
    (checker_footer_parse_entry_input s source widths.length bounded pointer rows)
    (checker_footer_parse_entry_apart s source widths bounded pointer rows metadata sourceEnd)
    (by rw [checker_footer_parse_entry_metadata]; exact metadata)
    (checker_footer_parse_entry_source s source widths.length bounded pointer rows)
    ((checker_footer_parse_entry_count s).trans rows) sourceRoom inputRoom

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual variable footer parser execution and strict-tail flags through word 2223. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerFooterParsedState (count : Nat) (s : MachineState) : MachineState :=
  tailValidatePrefix (tailParsedFieldsState count (checkerFooterParseEntry s)) 3
@[irreducible] def checkerFooterParserCycles (count : Nat) (s : MachineState) : Nat :=
  tailParsedFieldsCycles count (checkerFooterParseEntry s)+4
theorem checker_footer_parsed_eq (count : Nat) (s : MachineState) : checkerFooterParsedState count s=
    tailValidatePrefix (tailParsedFieldsState count (checkerFooterParseEntry s)) 3 := by
  rw [checkerFooterParsedState]
theorem checker_footer_parser_cycles_eq (count : Nat) (s : MachineState) : checkerFooterParserCycles count s=
    tailParsedFieldsCycles count (checkerFooterParseEntry s)+4 := by rw [checkerFooterParserCycles]
theorem checker_footer_parser_cycles_bound (count : Nat) (s : MachineState) :
    checkerFooterParserCycles count s≤17*count+4 := by
  rw [checker_footer_parser_cycles_eq]
  have bound := tail_parsed_fields_bound count (checkerFooterParseEntry s)
  omega

private theorem merged_ChainedCheckerFooterParseRun_parser_endpoint (count : Nat) (s : MachineState)
    (pc : s.pc=if count=0 then (4096+4*2202)+72 else (4096+4*2202)+4)
    (ready : TailParsedFieldsReady count s) :
    (tailValidatePrefix (tailParsedFieldsState count s) 3).pc=4096+4*2223 :=
  (tail_parsed_fields_validate_pc count s (4096+4*2202) pc ready).trans (by decide +kernel)

theorem checker_footer_parser_execution (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerFooterParserCycles widths.length s+fuel) (checkerFooterParseSetupState s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterParsedState widths.length s) coins
          return result.charge (checkerFooterParserCycles widths.length s) 0) := by
  have ready := checker_footer_parser_ready s source widths bounded pointer rows metadata sourceEnd small table
  have entryPC := checker_footer_parse_entry_pc s widths.length bounded rows pc enough
  rw [checking_manifest_image,checker_footer_parser_cycles_eq,
    show tailParsedFieldsCycles widths.length (checkerFooterParseEntry s)+4+fuel=
      1+(tailParsedFieldsCycles widths.length (checkerFooterParseEntry s)+3+fuel) by omega,
    checker_footer_parser_enter s pc enough,
    tail_parsed_fields_validate_execution chainedCheckerImage _ chained_checker_footer_parse_at
      widths.length (checkerFooterParseEntry s) entryPC ready,←checker_footer_parsed_eq]
  have chargeSum : 1+tailParsedFieldsCycles widths.length (checkerFooterParseEntry s)+3=
      tailParsedFieldsCycles widths.length (checkerFooterParseEntry s)+4 := by omega
  simp [Execution.charge,←Nat.add_assoc,chargeSum]

theorem checker_footer_parsed_pc (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s) :
    (checkerFooterParsedState widths.length s).pc=4096+4*2223 := by
  rw [checker_footer_parsed_eq]
  exact merged_ChainedCheckerFooterParseRun_parser_endpoint widths.length (checkerFooterParseEntry s)
    (checker_footer_parse_entry_pc s widths.length bounded rows pc enough)
    (checker_footer_parser_ready s source widths bounded pointer rows metadata sourceEnd small table)

theorem checker_footer_setup_parser_execution (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (11+checkerFooterParserCycles widths.length s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterParsedState widths.length s) coins
          return result.charge (11+checkerFooterParserCycles widths.length s) 0) := by
  rw [Nat.add_assoc,checker_footer_parse_setup_execution s pc enough,
    checker_footer_parser_execution s source widths bounded pointer rows metadata sourceEnd small table pc enough]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_footer_parser_content (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (endBytes : Nat) (endFit : endBytes<2^64)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+29*widths.length+endBytes)) :
    let plan := tailParsePlan widths [] (checkerFooterInput s source widths.length)
    (checkerFooterParsedState widths.length s).getReg .x24=(if plan.read=endBytes ∧
      (∀ index, index<plan.carry.length → plan.carry.getD index false=false) then 1#64 else 0#64) ∧
    ∀ query, (checkerFooterParsedState widths.length s).getByte query=
      writeParsedRows s.getByte (s.getReg .x8) plan.fields query := by
  have apart := checker_footer_parse_entry_apart s source widths bounded pointer rows metadata sourceEnd
  have endpoint : (checkerFooterParseEntry s).getReg .x19=
      (checkerFooterParseEntry s).getReg .x20+BitVec.ofNat 64 endBytes := by
    rw [checker_footer_parse_entry_register,checker_footer_parse_setup_end,
      checker_footer_parse_entry_source s source widths.length bounded pointer rows,endPointer,←BitVec.ofNat_add]
  have result := native_tail_parse_result widths [] (checkerFooterInput s source widths.length)
    (checkerFooterParseEntry s) (checker_footer_parse_entry_buffer s)
    (checker_footer_input_size s source widths.length) small (checker_footer_parse_entry_widths s widths table)
    (checker_footer_parse_entry_input s source widths.length bounded pointer rows) apart (by omega)
    endBytes endFit endpoint
  dsimp only
  rw [checker_footer_parsed_eq]
  refine ⟨result.1,?_⟩
  intro query
  rw [result.2,checker_footer_parse_entry_metadata]
  have memory : (checkerFooterParseEntry s).getByte=s.getByte := funext (checker_footer_parse_entry_byte s)
  rw [memory]

end CommitGolfCandidate.Chained.Native

end

section

/-! Bind actual footer parser descriptors and acceptance to the strict typed codec. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem checker_footer_spec_length (nodes : List Nat) : (InteriorCodec.footerSpec nodes).length=nodes.length := by
  simp only [InteriorCodec.footerSpec,List.length_map]
theorem checker_footer_spec_widths (nodes : List Nat) :
    (InteriorCodec.footerSpec nodes).map Prod.snd=nodes.map checkerFooterHighWidth := by
  rw [InteriorCodec.footerSpec,List.map_map]
  rfl
theorem checker_footer_low_count (nodes : List Nat) : lowCount (InteriorCodec.footerSpec nodes)=232*nodes.length := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    change 232+lowCount (InteriorCodec.footerSpec nodes)=232*(nodes.length+1)
    omega
theorem checker_footer_low_byte_count (nodes : List Nat) : lowCount (InteriorCodec.footerSpec nodes)/8=29*nodes.length := by
  rw [checker_footer_low_count]
  omega

def checkerFooterParsedPayload (nodes : List Nat) (proof : Proof) (s : MachineState) (source : Nat) :
    Payload (InteriorCodec.footerSpec nodes) :=
  fieldsFromRows (InteriorCodec.footerSpec nodes) (unpackBits (lowCount (InteriorCodec.footerSpec nodes)) proof)
    (tailParsePlan ((InteriorCodec.footerSpec nodes).map Prod.snd) [] (checkerFooterInput s source nodes.length)).fields

theorem checker_footer_parsed_descriptor (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*nodes.length+1≤checkingRawBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth)) :
    BytesAt (checkerFooterParsedState nodes.length s) (BitVec.ofNat 64 checkingMetadataBase)
      (descriptorBytes (highRows (checkerFooterParsedPayload nodes proof s source))) := by
  have memory := checker_footer_parse_entry_input s source nodes.length bounded pointer rows
  have apart := checker_footer_parse_entry_apart s source ((InteriorCodec.footerSpec nodes).map Prod.snd)
    (by simpa only [List.length_map,checker_footer_spec_length] using bounded) pointer
    (by simpa only [List.length_map,checker_footer_spec_length] using rows) metadata
    (by simpa only [List.length_map,checker_footer_spec_length] using sourceEnd)
  have result := parsed_payload_descriptor (InteriorCodec.footerSpec nodes) proof (checkerFooterInput s source nodes.length)
    (checkerFooterParseEntry s) (checker_footer_parse_entry_buffer s) (checker_footer_input_size s source nodes.length)
    (footer_fields_small nodes)
    (checker_footer_parse_entry_widths s _ (by rwa [checker_footer_spec_widths]))
    (by simpa only [checker_footer_spec_length] using memory) apart
    (by rw [checker_footer_spec_length]; omega)
  dsimp only at result
  rw [checker_footer_spec_length,checker_footer_parse_entry_metadata,metadata,←checker_footer_parsed_eq] at result
  exact result

theorem checker_footer_guarded_body_length (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (proofFit : source+proof.length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+proof.length))
    (enough : CheckerFooterLowBodyFits s) : 29*nodes.length≤proof.length := by
  have room : checkingRawBase+7424<2^64 := by decide +kernel
  have result := (checker_footer_low_body_fits_iff s source nodes.length (source+proof.length) bounded pointer rows
    endPointer (by omega) (by omega)).mp enough
  omega

theorem checker_footer_input_tail (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (body : 29*nodes.length≤proof.length) (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (index : Nat) (inside : index<(proof.drop (29*nodes.length)).length) :
    checkerFooterInput s source nodes.length index=byteBits ((proof.drop (29*nodes.length)).getD index 0) := by
  have bounded : 29*nodes.length+index<proof.length := by simp only [List.length_drop] at inside; omega
  unfold checkerFooterInput
  rw [BitVec.ofNat_add,byte_offset_add,memory _ bounded]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem checker_footer_parsed_accepts (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+proof.length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+proof.length))
    (enough : CheckerFooterLowBodyFits s) (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (accepted : (checkerFooterParsedState nodes.length s).getReg .x24=1#64) :
    unpack (InteriorCodec.footerSpec nodes) proof=some (checkerFooterParsedPayload nodes proof s source) ∧
      decode (InteriorCodec.footerSpec nodes) proof=checkerFooterParsedPayload nodes proof s source := by
  have body := checker_footer_guarded_body_length s source nodes proof bounded pointer rows proofFit endPointer enough
  have sourceEnd : source+30*nodes.length+1≤checkingRawBase := by omega
  have room : checkingRawBase<2^64 := by decide +kernel
  have apart := checker_footer_parse_entry_apart s source ((InteriorCodec.footerSpec nodes).map Prod.snd)
    (by simpa only [List.length_map,checker_footer_spec_length] using bounded) pointer
    (by simpa only [List.length_map,checker_footer_spec_length] using rows) metadata
    (by simpa only [List.length_map,checker_footer_spec_length] using sourceEnd)
  have endpoint : (checkerFooterParseEntry s).getReg .x19=(checkerFooterParseEntry s).getReg .x20+
      BitVec.ofNat 64 (proof.drop (lowCount (InteriorCodec.footerSpec nodes)/8)).length := by
    rw [checker_footer_parse_entry_register,checker_footer_parse_setup_end,
      checker_footer_parse_entry_source s source nodes.length bounded pointer rows,endPointer,←BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64)
    rw [List.length_drop,checker_footer_low_byte_count]
    omega
  have result := parsed_payload_accepts (InteriorCodec.footerSpec nodes) proof (checkerFooterInput s source nodes.length)
    (checkerFooterParseEntry s) (checker_footer_parse_entry_buffer s) (checker_footer_input_size s source nodes.length)
    (by intro field member; obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member; change 232%8=0; decide)
    (footer_fields_small nodes) (by rwa [checker_footer_low_byte_count])
    (checker_footer_parse_entry_widths s _ (by rwa [checker_footer_spec_widths]))
    (by simpa only [checker_footer_spec_length] using checker_footer_parse_entry_input s source nodes.length bounded pointer rows)
    apart (by rw [checker_footer_spec_length]; omega)
    (by simp only [List.length_drop]; omega) endpoint
    (by simpa only [checker_footer_low_byte_count] using checker_footer_input_tail s source nodes proof body memory)
  apply result
  rwa [checker_footer_spec_length,←checker_footer_parsed_eq]

theorem checker_footer_encoded_body_length (nodes : List Nat)
    (payload : Payload (InteriorCodec.footerSpec nodes)) : 29*nodes.length≤(encode payload).length := by
  rw [footer_descriptor_encoding,List.length_append,footer_low_bytes_length]
  omega

theorem checker_footer_encoded_fits (s : MachineState) (source : Nat) (nodes : List Nat)
    (payload : Payload (InteriorCodec.footerSpec nodes)) (bounded : nodes.length≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (proofFit : source+(encode payload).length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+(encode payload).length)) :
    CheckerFooterLowBodyFits s := by
  have body := checker_footer_encoded_body_length nodes payload
  have room : checkingRawBase<2^64 := by decide +kernel
  apply (checker_footer_low_body_fits_iff s source nodes.length (source+(encode payload).length)
    bounded pointer rows endPointer (by omega) (by omega)).mpr
  omega

theorem checker_footer_encoded_accepts (s : MachineState) (source : Nat) (nodes : List Nat)
    (payload : Payload (InteriorCodec.footerSpec nodes)) (bounded : nodes.length≤256)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source) (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+(encode payload).length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+(encode payload).length))
    (memory : BytesAt s (BitVec.ofNat 64 source) (encode payload)) :
    (checkerFooterParsedState nodes.length s).getReg .x24=1#64 := by
  have body := checker_footer_encoded_body_length nodes payload
  have sourceEnd : source+30*nodes.length+1≤checkingRawBase := by omega
  have room : checkingRawBase<2^64 := by decide +kernel
  have apart := checker_footer_parse_entry_apart s source ((InteriorCodec.footerSpec nodes).map Prod.snd)
    (by simpa only [List.length_map,checker_footer_spec_length] using bounded) pointer
    (by simpa only [List.length_map,checker_footer_spec_length] using rows) metadata
    (by simpa only [List.length_map,checker_footer_spec_length] using sourceEnd)
  have endpoint : (checkerFooterParseEntry s).getReg .x19=(checkerFooterParseEntry s).getReg .x20+
      BitVec.ofNat 64 ((encode payload).drop (lowCount (InteriorCodec.footerSpec nodes)/8)).length := by
    rw [checker_footer_parse_entry_register,checker_footer_parse_setup_end,
      checker_footer_parse_entry_source s source nodes.length bounded pointer rows,endPointer,←BitVec.ofNat_add]
    apply congrArg (BitVec.ofNat 64)
    rw [List.length_drop,checker_footer_low_byte_count]
    omega
  have result := parsed_payload_complete (InteriorCodec.footerSpec nodes) payload (checkerFooterInput s source nodes.length)
    (checkerFooterParseEntry s) (checker_footer_parse_entry_buffer s) (checker_footer_input_size s source nodes.length)
    (by intro field member; obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member; change 232%8=0; decide)
    (footer_fields_small nodes) (checker_footer_parse_entry_widths s _ (by rwa [checker_footer_spec_widths]))
    (by simpa only [checker_footer_spec_length] using checker_footer_parse_entry_input s source nodes.length bounded pointer rows)
    apart (by rw [checker_footer_spec_length]; omega) (by simp only [List.length_drop]; omega) endpoint
    (by simpa only [checker_footer_low_byte_count] using checker_footer_input_tail s source nodes (encode payload) body memory)
  simpa only [checker_footer_spec_length,←checker_footer_parsed_eq] using result

end CommitGolfCandidate.Chained.Native

end

section

/-! Preserve source bytes and inverse-entry registers through variable footer parsing. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem checker_footer_parsed_register (count : Nat) (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerFooterParsedState count s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_footer_parsed_eq,parsed_fields_register count _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    checker_footer_parse_entry_register,checker_footer_parse_setup_register _ _ (by decide)]
theorem checker_footer_parsed_saved_count (count : Nat) (s : MachineState) :
    (checkerFooterParsedState count s).getReg .x2=s.getReg .x22 := by
  rw [checker_footer_parsed_eq,parsed_fields_register count _ .x2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    checker_footer_parse_entry_register,checker_footer_parse_setup_saved_count]

theorem checker_footer_parsed_memory (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths) (query : Word) :
    (checkerFooterParsedState widths.length s).getByte query=
      writeParsedRows s.getByte (s.getReg .x8)
        (tailParsePlan widths [] (checkerFooterInput s source widths.length)).fields query := by
  have model := native_tail_parse_plan widths [] (checkerFooterInput s source widths.length)
    (checkerFooterParseEntry s) (checker_footer_parse_entry_buffer s)
    (checker_footer_input_size s source widths.length) small (checker_footer_parse_entry_widths s widths table)
    (checker_footer_parse_entry_input s source widths.length bounded pointer rows)
    (checker_footer_parse_entry_apart s source widths bounded pointer rows metadata sourceEnd) (by omega)
  have validation : (tailValidatePrefix (tailParsedFieldsState widths.length (checkerFooterParseEntry s)) 3).getByte query=
      (tailParsedFieldsState widths.length (checkerFooterParseEntry s)).getByte query := by
    simp only [MachineState.getByte,tail_validate_memory]
  rw [checker_footer_parsed_eq,validation,model.2.1,checker_footer_parse_entry_metadata]
  have memory : (checkerFooterParseEntry s).getByte=s.getByte := funext (checker_footer_parse_entry_byte s)
  rw [memory]

theorem checker_footer_parsed_byte_frame (s : MachineState) (source : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (query : Word) (apart : ∀ index, index<widths.length → query≠s.getReg .x8+BitVec.ofNat 64 (2*index)) :
    (checkerFooterParsedState widths.length s).getByte query=s.getByte query := by
  rw [checker_footer_parsed_memory s source widths bounded pointer rows metadata sourceEnd small table query]
  apply write_parsed_rows_preserves
  simpa only [tail_parse_plan_length] using apart

theorem checker_footer_parsed_source (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*nodes.length+1≤checkingRawBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+proof.length≤checkingRawBase) (memory : BytesAt s (BitVec.ofNat 64 source) proof) :
    BytesAt (checkerFooterParsedState nodes.length s) (BitVec.ofNat 64 source) proof := by
  have widthsSmall : ∀ width ∈ nodes.map checkerFooterHighWidth, width≤6 := by
    intro width member
    obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member
    exact checker_footer_high_width_small node
  intro index inside
  have preserved := checker_footer_parsed_byte_frame s source (nodes.map checkerFooterHighWidth)
    (by simpa only [List.length_map] using bounded) pointer (by simpa only [List.length_map] using rows)
    metadata (by simpa only [List.length_map] using sourceEnd) widthsSmall table
    (BitVec.ofNat 64 source+BitVec.ofNat 64 index) (by
      intro row before
      rw [metadata,←BitVec.ofNat_add,←BitVec.ofNat_add]
      have room : checkingMetadataBase+512<2^64 := by decide +kernel
      have order : checkingRawBase<checkingMetadataBase := by decide +kernel
      simp only [List.length_map] at before
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega))
  rw [List.length_map] at preserved
  exact preserved.trans (memory index inside)

end CommitGolfCandidate.Chained.Native

end

section

/-! Accepted footer branch and actual source/metadata/count resets through word 2229. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerFooterInverseSetupOps : List Instr :=
  [.ADDI .x5 .x18 0,.ADDI .x7 .x8 0,.ADDI .x22 .x2 0,.ADDI .x9 .x0 1]
@[irreducible] def checkerFooterInverseSetupPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i previous => execInstrBr previous (checkerFooterInverseSetupOps.getD i .EBREAK)) n
theorem checker_footer_inverse_setup_zero (s : MachineState) : checkerFooterInverseSetupPrefix 0 s=s := by
  unfold checkerFooterInverseSetupPrefix; rfl
theorem checker_footer_inverse_setup_succ (n : Nat) (s : MachineState) : checkerFooterInverseSetupPrefix (n+1) s=
    execInstrBr (checkerFooterInverseSetupPrefix n s) (checkerFooterInverseSetupOps.getD n .EBREAK) := by
  unfold checkerFooterInverseSetupPrefix; rfl
theorem checker_footer_inverse_setup_at : OpsAt chainedCheckerImage (4096+4*2225) checkerFooterInverseSetupOps :=
  chained_checker_slice_at 2225 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_footer_inverse_setup_register (s : MachineState) (reg : Reg) (kept : reg∉[.x5,.x7,.x9,.x22]) :
    (checkerFooterInverseSetupPrefix 4 s).getReg reg=s.getReg reg := by
  simp only [checker_footer_inverse_setup_succ,checker_footer_inverse_setup_zero]
  cases reg <;> simp at kept
  all_goals rfl
theorem checker_footer_inverse_setup_memory (s : MachineState) (n : Nat) (small : n≤4) (query : Word) :
    (checkerFooterInverseSetupPrefix n s).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 4) :
      (execInstrBr t (checkerFooterInverseSetupOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_footer_inverse_setup_zero]
  | succ n ih => rw [checker_footer_inverse_setup_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_footer_inverse_setup_pc (s : MachineState) (n : Nat) (small : n≤4) :
    (checkerFooterInverseSetupPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 4) :
      (execInstrBr t (checkerFooterInverseSetupOps.getD i.val .EBREAK)).pc=t.pc+4 := by fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_footer_inverse_setup_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_footer_inverse_setup_succ,step _ ⟨n,by omega⟩,ih (by omega)]
    change (s.pc+BitVec.ofNat 64 (4*n))+BitVec.ofNat 64 4=_
    rw [byte_offset_add]
    exact congrArg (fun offset => s.pc+BitVec.ofNat 64 offset) (by omega)

theorem checker_footer_inverse_setup_execution (s : MachineState) (pc : s.pc=4096+4*2225) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerFooterInverseSetupPrefix 4 s) coins
          return result.charge 4 0) := by
  conv_lhs => rw [←checker_footer_inverse_setup_zero s]
  apply execute_unit_steps (states := fun n => checkerFooterInverseSetupPrefix n s)
  intro i inside
  refine ⟨.base (checkerFooterInverseSetupOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_footer_inverse_setup_at i inside
    rw [checker_footer_inverse_setup_pc s i (by omega),pc]
  · rw [checker_footer_inverse_setup_succ]; interval_cases i <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def checkerFooterReconstructionEntry (count : Nat) (s : MachineState) : MachineState :=
  checkerFooterInverseSetupPrefix 4 ((checkerFooterParsedState count s).setPC ((checkerFooterParsedState count s).pc+8))
theorem checker_footer_reconstruction_entry_eq (count : Nat) (s : MachineState) : checkerFooterReconstructionEntry count s=
    checkerFooterInverseSetupPrefix 4 ((checkerFooterParsedState count s).setPC ((checkerFooterParsedState count s).pc+8)) := by
  rw [checkerFooterReconstructionEntry]

private theorem merged_ChainedCheckerFooterReconstructionEntry_setup_source (s : MachineState) : (checkerFooterInverseSetupPrefix 4 s).getReg .x5=s.getReg .x18 := by
  simp only [checker_footer_inverse_setup_succ,checker_footer_inverse_setup_zero]; exact BitVec.add_zero _
private theorem merged_ChainedCheckerFooterReconstructionEntry_setup_metadata (s : MachineState) : (checkerFooterInverseSetupPrefix 4 s).getReg .x7=s.getReg .x8 := by
  simp only [checker_footer_inverse_setup_succ,checker_footer_inverse_setup_zero]; exact BitVec.add_zero _
private theorem merged_ChainedCheckerFooterReconstructionEntry_setup_count (s : MachineState) : (checkerFooterInverseSetupPrefix 4 s).getReg .x22=s.getReg .x2 := by
  simp only [checker_footer_inverse_setup_succ,checker_footer_inverse_setup_zero]; exact BitVec.add_zero _
private theorem merged_ChainedCheckerFooterReconstructionEntry_setup_skip (s : MachineState) : (checkerFooterInverseSetupPrefix 4 s).getReg .x9=1#64 := by
  simp only [checker_footer_inverse_setup_succ,checker_footer_inverse_setup_zero]; rfl

theorem checker_footer_reconstruction_source (count : Nat) (s : MachineState) :
    (checkerFooterReconstructionEntry count s).getReg .x5=s.getReg .x18 := by
  rw [checker_footer_reconstruction_entry_eq,merged_ChainedCheckerFooterReconstructionEntry_setup_source,MachineState.getReg_setPC,checker_footer_parsed_register _ _ .x18 (by decide)]
theorem checker_footer_reconstruction_metadata (count : Nat) (s : MachineState) :
    (checkerFooterReconstructionEntry count s).getReg .x7=s.getReg .x8 := by
  rw [checker_footer_reconstruction_entry_eq,merged_ChainedCheckerFooterReconstructionEntry_setup_metadata,MachineState.getReg_setPC,checker_footer_parsed_register _ _ .x8 (by decide)]
theorem checker_footer_reconstruction_count (count : Nat) (s : MachineState) :
    (checkerFooterReconstructionEntry count s).getReg .x22=s.getReg .x22 := by
  rw [checker_footer_reconstruction_entry_eq,merged_ChainedCheckerFooterReconstructionEntry_setup_count,MachineState.getReg_setPC,checker_footer_parsed_saved_count]
theorem checker_footer_reconstruction_skip (count : Nat) (s : MachineState) :
    (checkerFooterReconstructionEntry count s).getReg .x9=1#64 := by
  rw [checker_footer_reconstruction_entry_eq,merged_ChainedCheckerFooterReconstructionEntry_setup_skip]
theorem checker_footer_reconstruction_output (count : Nat) (s : MachineState) :
    (checkerFooterReconstructionEntry count s).getReg .x6=s.getReg .x6 := by
  rw [checker_footer_reconstruction_entry_eq,checker_footer_inverse_setup_register _ .x6 (by decide),
    MachineState.getReg_setPC,checker_footer_parsed_register _ _ .x6 (by decide)]
theorem checker_footer_reconstruction_memory (count : Nat) (s : MachineState) (query : Word) :
    (checkerFooterReconstructionEntry count s).getMem query=(checkerFooterParsedState count s).getMem query := by
  rw [checker_footer_reconstruction_entry_eq,checker_footer_inverse_setup_memory _ 4 (by decide),MachineState.getMem_setPC]
theorem checker_footer_reconstruction_byte (count : Nat) (s : MachineState) (query : Word) :
    (checkerFooterReconstructionEntry count s).getByte query=(checkerFooterParsedState count s).getByte query := by
  simp only [MachineState.getByte,checker_footer_reconstruction_memory]
theorem checker_footer_reconstruction_pc (count : Nat) (s : MachineState)
    (pc : (checkerFooterParsedState count s).pc=4096+4*2223) :
    (checkerFooterReconstructionEntry count s).pc=4096+4*2229 := by
  rw [checker_footer_reconstruction_entry_eq,checker_footer_inverse_setup_pc _ 4 (by decide)]
  change ((checkerFooterParsedState count s).pc+8)+16=_
  rw [pc]; rfl

private theorem merged_ChainedCheckerFooterReconstructionEntry_accepted_footer_guard (s : MachineState) (pc : s.pc=4096+4*2223)
    (accepted : s.getReg .x24=1#64) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (s.setPC (s.pc+8)) coins
          return result.charge 1 0) := by
  have fetched : fetch chainedCheckerImage s=some (.base (.BNE .x24 .x0 8)) :=
    chained_checker_ops_at 2223 (by rw [chained_checker_ops_length]; decide) s pc
  have step : ordinaryStep s (.base (.BNE .x24 .x0 8))=some (s.setPC (s.pc+8)) := by
    change some (if s.getReg .x24 != s.getReg .x0 then _ else _)=_
    rw [accepted]; rfl
  rw [show 1+fuel=fuel+1 by omega]
  exact execute_ordinary_step _ _ _ _ fuel coins fetched step

theorem checker_footer_reconstruction_entry_execution (count : Nat) (s : MachineState)
    (pc : (checkerFooterParsedState count s).pc=4096+4*2223)
    (accepted : (checkerFooterParsedState count s).getReg .x24=1#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) (checkerFooterParsedState count s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterReconstructionEntry count s) coins
          return result.charge 5 0) := by
  have guardedPC : ((checkerFooterParsedState count s).setPC ((checkerFooterParsedState count s).pc+8)).pc=4096+4*2225 := by
    change (checkerFooterParsedState count s).pc+8=_
    rw [pc]; rfl
  rw [checking_manifest_image,show 5+fuel=1+(4+fuel) by omega,merged_ChainedCheckerFooterReconstructionEntry_accepted_footer_guard _ pc accepted,
    checker_footer_inverse_setup_execution _ guardedPC,←checker_footer_reconstruction_entry_eq]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native

end

section

/-! Supplied low bytes, parsed descriptors and preserved output establish footer inverse readiness. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem checker_footer_spec_aligned (nodes : List Nat) : ∀ field ∈ InteriorCodec.footerSpec nodes, field.1%8=0 := by
  intro field member
  obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member
  change 232%8=0
  decide

theorem checker_footer_low_body (s : MachineState) (source : Nat) (nodes : List Nat) (proof : Proof)
    (body : 29*nodes.length≤proof.length) :
    lowBytes (checkerFooterParsedPayload nodes proof s source)=proof.take (29*nodes.length) := by
  have widths := tail_parse_plan_widths ((InteriorCodec.footerSpec nodes).map Prod.snd) []
    (checkerFooterInput s source nodes.length) (checker_footer_input_size s source nodes.length) (by
      intro width member
      obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
      exact footer_fields_small nodes field belongs)
  have result := low_bytes_from_rows (InteriorCodec.footerSpec nodes) proof _ widths
    (checker_footer_spec_aligned nodes) (by rwa [checker_footer_low_byte_count])
  simpa only [checkerFooterParsedPayload,checker_footer_low_byte_count] using result

private theorem merged_ChainedCheckerFooterInverseReady_raw_padding_empty_fields (fields : List RawField) (s : MachineState) (base : Word)
    (empty : ∀ field ∈ fields, field.padding=[]) : RawPaddingAt s base fields := by
  induction fields generalizing base with
  | nil => trivial
  | cons field fields ih =>
    constructor
    · rw [empty field (by simp)]
      intro index inside
      simp at inside
    · apply ih
      intro next member
      exact empty next (by simp [member])

theorem checker_footer_inverse_ready (s : MachineState) (source outputBase : Nat) (nodes : List Nat) (proof completed : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+proof.length+512≤checkingRawBase) (body : 29*nodes.length≤proof.length)
    (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 (outputBase+completed.length))
    (outputEnd : outputBase+completed.length+30*nodes.length≤checkingMetadataBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (previous : BytesAt s (BitVec.ofNat 64 outputBase) completed) :
    InverseFieldsReady (footerRawFields nodes (checkerFooterParsedPayload nodes proof s source)) [] completed
      (checkerFooterReconstructionEntry nodes.length s) source outputBase checkingMetadataBase := by
  let footer := checkerFooterParsedPayload nodes proof s source
  have sourceEnd : source+30*nodes.length+1≤checkingRawBase := by omega
  have low : rawFieldsLow (footerRawFields nodes footer)=lowBytes footer := footer_raw_fields_low nodes footer
  have high : rawFieldsMeta (footerRawFields nodes footer)=descriptorBytes (highRows footer) := footer_raw_fields_meta nodes footer
  have room : checkingMetadataBase+512<2^64 := by decide +kernel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [checker_footer_reconstruction_source]; exact pointer
  · rw [checker_footer_reconstruction_output]; exact outputPointer
  · rw [checker_footer_reconstruction_metadata]; exact metadata
  · rw [low,List.append_nil,checker_footer_low_body s source nodes proof body]
    have original := checker_footer_parsed_source s source nodes proof bounded pointer rows metadata sourceEnd table (by omega) memory
    intro index inside
    have before : index<proof.length := by rw [List.length_take] at inside; omega
    rw [checker_footer_reconstruction_byte,original index before]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take]
    rw [ite_eq_left (by rw [List.length_take] at inside; omega)]
  · have small : ∀ width ∈ nodes.map checkerFooterHighWidth, width≤6 := by
      intro width member
      obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member
      exact checker_footer_high_width_small node
    intro index inside
    rw [checker_footer_reconstruction_byte]
    have preserved := checker_footer_parsed_byte_frame s source (nodes.map checkerFooterHighWidth)
      (by simpa only [List.length_map] using bounded) pointer (by simpa only [List.length_map] using rows)
      metadata (by simpa only [List.length_map] using sourceEnd) small table
      (BitVec.ofNat 64 outputBase+BitVec.ofNat 64 index) (by
        intro row before
        rw [metadata,←BitVec.ofNat_add,←BitVec.ofNat_add]
        simp only [List.length_map] at before
        exact word_of_nat_ne _ _ (by omega) (by omega) (by omega))
    rw [List.length_map] at preserved
    exact preserved.trans (previous index inside)
  · rw [high]
    have original := checker_footer_parsed_descriptor s source nodes proof bounded pointer rows metadata sourceEnd table
    intro index inside
    rw [checker_footer_reconstruction_byte]
    exact original index inside
  · apply merged_ChainedCheckerFooterInverseReady_raw_padding_empty_fields
    exact (footer_layout_inverse_shapes (footer_raw_fields_layout nodes footer)).2
  · rw [low,footer_low_bytes_length,List.length_nil,Nat.add_zero]
    omega
  · rwa [footer_raw_fields_length]
  · rw [footer_raw_fields_count]
    omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Installed footer inverse execution, terminal PC and typed output with prior records retained. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerFooterReconstructedState (count : Nat) (s : MachineState) : MachineState :=
  inverseFooterRowsState count (inverseFooterEntryState (checkerFooterReconstructionEntry count s))
theorem checker_footer_reconstructed_eq (count : Nat) (s : MachineState) : checkerFooterReconstructedState count s=
    inverseFooterRowsState count (inverseFooterEntryState (checkerFooterReconstructionEntry count s)) := by
  rw [checkerFooterReconstructedState]

theorem checker_footer_inverse_control_ready (count : Nat) (s : MachineState) (source output : Nat)
    (bounded : count≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 count)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (destination : s.getReg .x6=BitVec.ofNat 64 output)
    (sourceRoom : source+29*count+1≤MEMORY_BYTES) (outputRoom : output+30*count≤MEMORY_BYTES) :
    InverseFooterReady count (checkerFooterReconstructionEntry count s) source output checkingMetadataBase := by
  refine ⟨?_,?_,?_,checker_footer_reconstruction_skip count s,?_,sourceRoom,outputRoom,?_⟩
  · rw [checker_footer_reconstruction_source]; exact pointer
  · rw [checker_footer_reconstruction_output]; exact destination
  · rw [checker_footer_reconstruction_metadata]; exact metadata
  · rw [checker_footer_reconstruction_count]; exact rows
  · have room : checkingMetadataBase+512≤MEMORY_BYTES := by decide +kernel
    omega

private theorem merged_ChainedCheckerFooterInverseRun_footer_rows_end_pc (count : Nat) (s : MachineState) (source output metadata : Nat) (base : Word)
    (ready : InverseFooterReady count s source output metadata)
    (pc : s.pc=if count=0 then base+492 else base+4) :
    (inverseFooterRowsState count s).pc=base+492 := by
  induction count generalizing s source output metadata with
  | zero => rw [inverse_footer_rows_zero]; simpa using pc
  | succ count ih =>
    have room : MEMORY_BYTES<2^64 := by decide +kernel
    have nextPC := inverse_footer_field_pc s base count (by simpa using pc) ready.count (by have := ready.metaRoom; omega)
    rw [inverse_footer_rows_succ]
    exact ih _ _ _ _ (inverse_footer_ready_step count s source output metadata ready) nextPC

private theorem merged_ChainedCheckerFooterInverseRun_footer_entry_ready (count : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady count s source output metadata) :
    InverseFooterReady count (inverseFooterEntryState s) source output metadata := by
  refine ⟨?_,?_,?_,?_,?_,ready.sourceRoom,ready.outputRoom,ready.metaRoom⟩
  · rw [inverse_footer_entry_register]; exact ready.sourcePointer
  · rw [inverse_footer_entry_register]; exact ready.outputPointer
  · rw [inverse_footer_entry_register]; exact ready.metaPointer
  · rw [inverse_footer_entry_register]; exact ready.skip
  · rw [inverse_footer_entry_register]; exact ready.count

private theorem merged_ChainedCheckerFooterInverseRun_installed_footer_end_pc (count : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady count s source output metadata) (pc : s.pc=4096+4*2229) :
    (inverseFooterRowsState count (inverseFooterEntryState s)).pc=4096+4*2352 := by
  have room : MEMORY_BYTES<2^64 := by decide +kernel
  have start := inverse_footer_entry_pc s count ready.count (by have := ready.metaRoom; omega)
  rw [pc] at start
  exact (merged_ChainedCheckerFooterInverseRun_footer_rows_end_pc count _ source output metadata (4096+4*2229)
    (merged_ChainedCheckerFooterInverseRun_footer_entry_ready count s source output metadata ready) start).trans (by decide +kernel)

theorem checker_footer_reconstructed_pc (count : Nat) (s : MachineState) (source output : Nat)
    (ready : InverseFooterReady count (checkerFooterReconstructionEntry count s) source output checkingMetadataBase)
    (pc : (checkerFooterParsedState count s).pc=4096+4*2223) :
    (checkerFooterReconstructedState count s).pc=4096+4*2352 := by
  rw [checker_footer_reconstructed_eq]
  exact merged_ChainedCheckerFooterInverseRun_installed_footer_end_pc count _ source output checkingMetadataBase ready (checker_footer_reconstruction_pc count s pc)

theorem checker_footer_inverse_execution (count : Nat) (s : MachineState) (source output : Nat)
    (ready : InverseFooterReady count (checkerFooterReconstructionEntry count s) source output checkingMetadataBase)
    (pc : (checkerFooterParsedState count s).pc=4096+4*2223) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (1+122*count+fuel) (checkerFooterReconstructionEntry count s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterReconstructedState count s) coins
          return result.charge (1+122*count) 0) := by
  rw [checking_manifest_image,checker_footer_reconstructed_eq]
  exact inverse_footer_execution chainedCheckerImage _ chained_checker_footer_inverse_at count _ source output checkingMetadataBase
    ready (checker_footer_reconstruction_pc count s pc) fuel coins

theorem checker_footer_reconstructed_content (s : MachineState) (source outputBase : Nat) (nodes : List Nat) (proof completed : Proof)
    (ready : InverseFieldsReady (footerRawFields nodes (checkerFooterParsedPayload nodes proof s source)) [] completed
      (checkerFooterReconstructionEntry nodes.length s) source outputBase checkingMetadataBase) :
    InverseFieldsReady [] [] (completed++rawFieldsBytes (footerRawFields nodes (checkerFooterParsedPayload nodes proof s source)))
      (checkerFooterReconstructedState nodes.length s) (source+29*nodes.length) outputBase (checkingMetadataBase+2*nodes.length) := by
  rw [checker_footer_reconstructed_eq]
  exact native_inverse_footer_payload nodes _ [] completed _ source outputBase checkingMetadataBase ready
    (checker_footer_reconstruction_skip nodes.length s)

theorem checker_footer_parser_inverse_execution (s : MachineState) (source output : Nat) (widths : List Nat)
    (bounded : widths.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 widths.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+30*widths.length+1≤checkingRawBase)
    (small : ∀ width ∈ widths, width≤6) (table : ParseWidthsAt s (s.getReg .x8) widths)
    (destination : s.getReg .x6=BitVec.ofNat 64 output) (outputRoom : output+30*widths.length≤MEMORY_BYTES)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s)
    (accepted : (checkerFooterParsedState widths.length s).getReg .x24=1#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check)
      (11+checkerFooterParserCycles widths.length s+5+(1+122*widths.length)+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterReconstructedState widths.length s) coins
          return result.charge (11+checkerFooterParserCycles widths.length s+5+(1+122*widths.length)) 0) := by
  have parsedPC := checker_footer_parsed_pc s source widths bounded pointer rows metadata sourceEnd small table pc enough
  have sourceRoom : source+29*widths.length+1≤MEMORY_BYTES := by
    have room : checkingRawBase≤MEMORY_BYTES := by decide +kernel
    omega
  have ready := checker_footer_inverse_control_ready widths.length s source output bounded pointer rows metadata destination sourceRoom outputRoom
  rw [show 11+checkerFooterParserCycles widths.length s+5+(1+122*widths.length)+fuel=
    (11+checkerFooterParserCycles widths.length s)+(5+((1+122*widths.length)+fuel)) by omega,
    checker_footer_setup_parser_execution s source widths bounded pointer rows metadata sourceEnd small table pc enough,
    checker_footer_reconstruction_entry_execution _ s parsedPC accepted,checker_footer_inverse_execution _ s source output ready parsedPC]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_footer_parser_inverse_bound (count : Nat) (s : MachineState) :
    11+checkerFooterParserCycles count s+5+(1+122*count)≤139*count+21 := by
  have bound := checker_footer_parser_cycles_bound count s
  omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Accepted supplied footer bytes refine the installed decoder through inverse completion. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_footer_decode_complete (s : MachineState) (source outputBase : Nat) (nodes : List Nat) (proof completed : Proof)
    (bounded : nodes.length≤256) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (rows : s.getReg .x22=BitVec.ofNat 64 nodes.length)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (table : ParseWidthsAt s (s.getReg .x8) (nodes.map checkerFooterHighWidth))
    (proofFit : source+proof.length+512≤checkingRawBase)
    (endPointer : s.getReg .x15+s.getReg .x17=BitVec.ofNat 64 (source+proof.length))
    (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 (outputBase+completed.length))
    (outputEnd : outputBase+completed.length+30*nodes.length≤checkingMetadataBase)
    (memory : BytesAt s (BitVec.ofNat 64 source) proof)
    (previous : BytesAt s (BitVec.ofNat 64 outputBase) completed)
    (pc : s.pc=4096+4*2190) (enough : CheckerFooterLowBodyFits s)
    (accepted : (checkerFooterParsedState nodes.length s).getReg .x24=1#64) :
    let footer := checkerFooterParsedPayload nodes proof s source
    ∃ cycles, cycles≤139*nodes.length+21 ∧
      (∀ fuel coins, execute (Artifact.submission.image .check) (cycles+fuel) s coins=
        (do let result ← execute (Artifact.submission.image .check) fuel (checkerFooterReconstructedState nodes.length s) coins
            return result.charge cycles 0)) ∧
      (checkerFooterReconstructedState nodes.length s).pc=4096+4*2352 ∧
      unpack (InteriorCodec.footerSpec nodes) proof=some footer ∧
      BytesAt (checkerFooterReconstructedState nodes.length s) (BitVec.ofNat 64 outputBase)
        (completed++rawFieldsBytes (footerRawFields nodes footer)) ∧
      (checkerFooterReconstructedState nodes.length s).getReg .x5=BitVec.ofNat 64 (source+29*nodes.length) ∧
      (checkerFooterReconstructedState nodes.length s).getReg .x6=BitVec.ofNat 64 (outputBase+completed.length+30*nodes.length) ∧
      (checkerFooterReconstructedState nodes.length s).getReg .x7=BitVec.ofNat 64 (checkingMetadataBase+2*nodes.length) ∧
      (checkerFooterReconstructedState nodes.length s).getReg .x22=0#64 := by
  have body := checker_footer_guarded_body_length s source nodes proof bounded pointer rows proofFit endPointer enough
  have sourceEnd : source+30*nodes.length+1≤checkingRawBase := by omega
  have room : checkingMetadataBase+512≤MEMORY_BYTES := by decide +kernel
  have order : checkingRawBase≤checkingMetadataBase := by decide +kernel
  have sourceRoom : source+29*nodes.length+1≤MEMORY_BYTES := by omega
  have outputRoom : outputBase+completed.length+30*nodes.length≤MEMORY_BYTES := by omega
  have widthsSmall : ∀ width ∈ nodes.map checkerFooterHighWidth, width≤6 := by
    intro width member
    obtain ⟨node,belongs,rfl⟩ := List.mem_map.mp member
    exact checker_footer_high_width_small node
  have parsedPC := checker_footer_parsed_pc s source (nodes.map checkerFooterHighWidth)
    (by simpa only [List.length_map] using bounded) pointer (by simpa only [List.length_map] using rows) metadata
    (by simpa only [List.length_map] using sourceEnd) widthsSmall table pc enough
  rw [List.length_map] at parsedPC
  have control := checker_footer_inverse_control_ready nodes.length s source (outputBase+completed.length)
    bounded pointer rows metadata outputPointer sourceRoom outputRoom
  have ready := checker_footer_inverse_ready s source outputBase nodes proof completed bounded pointer rows metadata table
    proofFit body outputStart outputPointer outputEnd memory previous
  have content := checker_footer_reconstructed_content s source outputBase nodes proof completed ready
  have entryControl : InverseFooterReady nodes.length
      (inverseFooterEntryState (checkerFooterReconstructionEntry nodes.length s)) source (outputBase+completed.length) checkingMetadataBase := by
    refine ⟨?_,?_,?_,?_,?_,sourceRoom,outputRoom,control.metaRoom⟩
    · rw [inverse_footer_entry_register]; exact control.sourcePointer
    · rw [inverse_footer_entry_register]; exact control.outputPointer
    · rw [inverse_footer_entry_register]; exact control.metaPointer
    · rw [inverse_footer_entry_register]; exact control.skip
    · rw [inverse_footer_entry_register]; exact control.count
  have finalControl := inverse_footer_rows_ready nodes.length _ source (outputBase+completed.length) checkingMetadataBase entryControl
  rw [←checker_footer_reconstructed_eq] at finalControl
  dsimp only
  refine ⟨11+checkerFooterParserCycles nodes.length s+5+(1+122*nodes.length),
    checker_footer_parser_inverse_bound nodes.length s,?_,checker_footer_reconstructed_pc _ s source _ control parsedPC,
    (checker_footer_parsed_accepts s source nodes proof bounded pointer rows metadata table proofFit endPointer enough memory accepted).1,
    content.output,content.sourcePointer,?_,content.metaPointer,finalControl.count⟩
  · intro fuel coins
    have result := checker_footer_parser_inverse_execution s source (outputBase+completed.length) (nodes.map checkerFooterHighWidth)
      (by simpa only [List.length_map] using bounded) pointer (by simpa only [List.length_map] using rows) metadata
      (by simpa only [List.length_map] using sourceEnd) widthsSmall table outputPointer
      (by simpa only [List.length_map] using outputRoom) pc enough (by simpa only [List.length_map] using accepted) fuel coins
    simpa only [List.length_map] using result
  · simpa only [List.length_append,footer_raw_fields_length,Nat.add_assoc] using content.outputPointer

end CommitGolfCandidate.Chained.Native

end
