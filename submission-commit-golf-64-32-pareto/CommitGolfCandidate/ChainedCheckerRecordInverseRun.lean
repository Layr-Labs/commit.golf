import CommitGolfCandidate.ChainedCheckerArtifact
import CommitGolfCandidate.ChainedRecordParseSetup
import CommitGolfCandidate.ChainedPacketBounds
import CommitGolf.Artifact
import CommitGolfCandidate.ChainedTailParseExecution
import CommitGolfCandidate.ChainedInverseMemoryFrame

section

/-! Actual six-instruction parser setup preserves initialized width memory. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerRecordSetupOps : List Instr :=
  [.ADDI .x20 .x18 479,.ADDI .x19 .x18 482,.ADDI .x21 .x8 0,
   .ADDI .x22 .x0 17,.ADDI .x23 .x0 0,.ADDI .x25 .x0 0]

@[irreducible] def checkerRecordSetupState (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i previous => execInstrBr previous (checkerRecordSetupOps.getD i .EBREAK)) n

theorem checker_record_setup_zero (s : MachineState) : checkerRecordSetupState 0 s=s := by
  unfold checkerRecordSetupState
  rfl

theorem checker_record_setup_succ (n : Nat) (s : MachineState) :
    checkerRecordSetupState (n+1) s=
      execInstrBr (checkerRecordSetupState n s) (checkerRecordSetupOps.getD n .EBREAK) := by
  unfold checkerRecordSetupState
  rfl

theorem checker_record_setup_at :
    OpsAt chainedCheckerImage (4096+4*109) checkerRecordSetupOps := by
  exact chained_checker_slice_at 109 6 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

private theorem merged_ChainedCheckerRecordSetup_setup_step_pc (s : MachineState) (i : Fin 6) :
    (execInstrBr s (checkerRecordSetupOps.getD i.val .EBREAK)).pc=s.pc+4 := by
  fin_cases i <;> rfl

theorem checker_record_setup_pc (s : MachineState) (n : Nat) (small : n≤6) :
    (checkerRecordSetupState n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_record_setup_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_record_setup_succ,merged_ChainedCheckerRecordSetup_setup_step_pc _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1

theorem checker_record_setup_memory (s : MachineState) (n : Nat) (small : n≤6) (query : Word) :
    (checkerRecordSetupState n s).getByte query=s.getByte query := by
  have step (state : MachineState) (i : Fin 6) :
      (execInstrBr state (checkerRecordSetupOps.getD i.val .EBREAK)).getByte query=state.getByte query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_record_setup_zero]
  | succ n ih => rw [checker_record_setup_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_record_setup_source (s : MachineState) :
    (checkerRecordSetupState 6 s).getReg .x20=s.getReg .x18+479 := by
  simp only [checker_record_setup_succ,checker_record_setup_zero]
  rfl

theorem checker_record_setup_end (s : MachineState) :
    (checkerRecordSetupState 6 s).getReg .x19=(checkerRecordSetupState 6 s).getReg .x20+3 := by
  simp only [checker_record_setup_succ,checker_record_setup_zero]
  change s.getReg .x18+482=s.getReg .x18+479+3
  rw [BitVec.add_assoc]
  rfl

theorem checker_record_setup_metadata (s : MachineState) :
    (checkerRecordSetupState 6 s).getReg .x21=s.getReg .x8 := by
  simp only [checker_record_setup_succ,checker_record_setup_zero]
  exact BitVec.add_zero _

theorem checker_record_setup_count (s : MachineState) :
    (checkerRecordSetupState 6 s).getReg .x22=17#64 := by
  simp only [checker_record_setup_succ,checker_record_setup_zero]
  rfl

theorem checker_record_setup_buffer (s : MachineState) : TailParseBuffer (checkerRecordSetupState 6 s) [] := by
  constructor
  · simp only [checker_record_setup_succ,checker_record_setup_zero]
    rfl
  · simp only [checker_record_setup_succ,checker_record_setup_zero]
    rfl
  · decide

theorem checker_record_setup_widths (s : MachineState)
    (table : ParseWidthsAt s (s.getReg .x8) (InteriorCodec.recordSpec.map Prod.snd)) :
    ParseWidthsAt (checkerRecordSetupState 6 s) ((checkerRecordSetupState 6 s).getReg .x21)
      (InteriorCodec.recordSpec.map Prod.snd) := by
  intro index inside
  rw [checker_record_setup_metadata,checker_record_setup_memory s 6 (by decide)]
  exact table index inside

theorem checker_record_setup_execution (s : MachineState) (pc : s.pc=4096+4*109)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (6+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRecordSetupState 6 s) coins
          return result.charge 6 0) := by
  conv_lhs => rw [←checker_record_setup_zero s]
  apply execute_unit_steps (states := fun n => checkerRecordSetupState n s)
  intro i inside
  refine ⟨.base (checkerRecordSetupOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_record_setup_at i (by change i<6; exact inside)
    rw [checker_record_setup_pc s i (by omega),pc]
  · rw [checker_record_setup_succ]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native

end

section

/-! Physical checking workspaces for every admissible position count. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

def checkingRawBase : Nat := Artifact.submission.layout.proof+2^33
def checkingMetadataBase : Nat := 2^35

theorem checking_public_regions :
    32768≤Artifact.submission.layout.commitment ∧
    Artifact.submission.layout.commitment+32≤Artifact.submission.layout.indices ∧
    Artifact.submission.layout.indices+8*LENGTH≤Artifact.submission.layout.values ∧
    Artifact.submission.layout.values+256*LENGTH≤Artifact.submission.layout.proof := by decide +kernel

theorem checking_small_workspaces :
    31*8≤256 ∧ 256+64≤4096 ∧ 4096+512*8≤12544 ∧
    12544+64≤16384 ∧ 16384+512*32≤32768 := by decide +kernel

theorem checking_source_before_raw (count length : Nat) (small : count≤LENGTH)
    (bounded : length≤482*count+3776) :
    Artifact.submission.layout.proof+length+512≤checkingRawBase := by
  have maximum : 482*LENGTH+3776+512≤2^33 := by decide +kernel
  unfold checkingRawBase
  omega

theorem checking_raw_before_metadata (count : Nat) (small : count≤LENGTH) :
    checkingRawBase+498*count+30*256≤checkingMetadataBase := by
  have maximum : checkingRawBase+498*LENGTH+30*256≤checkingMetadataBase := by decide +kernel
  omega

theorem checking_metadata_room : checkingMetadataBase+1056≤2^64 := by decide +kernel

theorem checking_metadata_parts :
    2*256≤1024 ∧ checkingMetadataBase+1024+4*8=checkingMetadataBase+1056 := by
  constructor
  · decide
  · omega

theorem checking_packet_source_before_raw (positions : Positions) :
    Artifact.submission.layout.proof+InteriorCodec.proofLength positions+512≤checkingRawBase := by
  apply checking_source_before_raw positions.card
  · simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ positions)
  · exact (InteriorCodec.packet_length_range positions).2

theorem checking_packet_raw_room (positions : Positions) :
    checkingRawBase+498*positions.card+30*256≤checkingMetadataBase := by
  apply checking_raw_before_metadata
  simpa only [Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ positions)

end CommitGolfCandidate.Chained.Native

end

section

/-! Delivered record-loop initialization establishes the native parser premises. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordReadyState (s : MachineState) : MachineState :=
  checkerRecordSetupState 6 (widthTableState recordWidths (execInstrBr s (.ADDI .x7 .x8 0)))

theorem checker_record_ready_eq (s : MachineState) : checkerRecordReadyState s=
    checkerRecordSetupState 6 (widthTableState recordWidths (execInstrBr s (.ADDI .x7 .x8 0))) := by
  rw [checkerRecordReadyState]

private theorem merged_ChainedCheckerRecordReady_reset_pointer (s : MachineState) :
    (execInstrBr s (.ADDI .x7 .x8 0)).getReg .x7=s.getReg .x8 := by
  exact BitVec.add_zero _

theorem checker_record_ready_source (s : MachineState) :
    (checkerRecordReadyState s).getReg .x20=s.getReg .x18+479 := by
  rw [checker_record_ready_eq,checker_record_setup_source,
    width_table_register recordWidths _ .x18 (by decide) (by decide)]
  rfl

theorem checker_record_ready_end (s : MachineState) :
    (checkerRecordReadyState s).getReg .x19=(checkerRecordReadyState s).getReg .x20+3 := by
  rw [checker_record_ready_eq,checker_record_setup_end]

theorem checker_record_ready_count (s : MachineState) :
    (checkerRecordReadyState s).getReg .x22=17#64 := by
  rw [checker_record_ready_eq,checker_record_setup_count]

theorem checker_record_ready_buffer (s : MachineState) : TailParseBuffer (checkerRecordReadyState s) [] := by
  rw [checker_record_ready_eq]
  exact checker_record_setup_buffer _

theorem checker_record_ready_metadata (s : MachineState) :
    (checkerRecordReadyState s).getReg .x21=s.getReg .x8 := by
  rw [checker_record_ready_eq,checker_record_setup_metadata,
    width_table_register recordWidths _ .x8 (by decide) (by decide)]
  rfl

theorem checker_record_ready_widths (s : MachineState) :
    ParseWidthsAt (checkerRecordReadyState s) ((checkerRecordReadyState s).getReg .x21)
      (InteriorCodec.recordSpec.map Prod.snd) := by
  rw [checker_record_ready_eq]
  apply checker_record_setup_widths
  rw [width_table_register recordWidths _ .x8 (by decide) (by decide)]
  have table := native_record_widths (execInstrBr s (.ADDI .x7 .x8 0))
  rw [merged_ChainedCheckerRecordReady_reset_pointer] at table
  exact table

theorem checker_record_ready_memory (s : MachineState) (query : Word)
    (away : ∀ index, index<17 → query≠s.getReg .x8+BitVec.ofNat 64 (2*index+1)) :
    (checkerRecordReadyState s).getByte query=s.getByte query := by
  rw [checker_record_ready_eq,checker_record_setup_memory _ 6 (by decide),width_table_byte_frame]
  · rfl
  · intro index inside
    rw [merged_ChainedCheckerRecordReady_reset_pointer]
    exact away index (by rwa [record_widths_count] at inside)

theorem checker_record_ready_input (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (sourcePointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    ParseInputAt (checkerRecordReadyState s) ((checkerRecordReadyState s).getReg .x20) input 17 := by
  intro index inside
  rw [checker_record_ready_source,checker_record_ready_memory]
  · exact memory index inside
  · intro row bounded
    have ordering : checkingRawBase<checkingMetadataBase := by decide +kernel
    have room := checking_metadata_room
    rw [sourcePointer,metadata]
    change BitVec.ofNat 64 source+BitVec.ofNat 64 479+BitVec.ofNat 64 index≠
      BitVec.ofNat 64 checkingMetadataBase+BitVec.ofNat 64 (2*row+1)
    simp only [←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_record_ready_pc (s : MachineState) (pc : s.pc=4096+4*57) :
    (checkerRecordReadyState s).pc=4096+4*115 := by
  rw [checker_record_ready_eq,checker_record_setup_pc _ 6 (by decide),width_table_pc,record_widths_count]
  change (s.pc+4)+204+24=4096+4*115
  rw [pc]
  rfl

theorem checker_record_ready_execution (s : MachineState) (pc : s.pc=4096+4*57)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (58+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordReadyState s) coins
          return result.charge 58 0) := by
  rw [checking_manifest_image]
  have resetPC : (execInstrBr s (.ADDI .x7 .x8 0)).pc=4096+4*58 := by
    change s.pc+4=_
    rw [pc]
    rfl
  have fetched : fetch chainedCheckerImage s=some (.base (.ADDI .x7 .x8 0)) := by
    exact chained_checker_ops_at 57 (by rw [chained_checker_ops_length]; decide) s pc
  have reset (rest : Nat) : execute chainedCheckerImage (1+rest) s coins=
      (do let result ← execute chainedCheckerImage rest (execInstrBr s (.ADDI .x7 .x8 0)) coins
          return result.charge 1 0) := by
    rw [show 1+rest=rest+1 by omega]
    conv_lhs => rw [execute,fetched]
    rfl
  have tablePC : (widthTableState recordWidths (execInstrBr s (.ADDI .x7 .x8 0))).pc=4096+4*109 := by
    rw [width_table_pc,record_widths_count,resetPC]
    rfl
  rw [show 58+fuel=1+(51+(6+fuel)) by omega,reset,
    native_record_widths_execution chainedCheckerImage _ chained_checker_record_widths_at _
      checkingMetadataBase (by rw [merged_ChainedCheckerRecordReady_reset_pointer]; exact metadata) (by decide +kernel) resetPC,
    checker_record_setup_execution _ tablePC,←checker_record_ready_eq]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native

end

section

/-! Physical native-parser readiness after the actual word-115 entry branch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192

@[irreducible] def checkerRecordParseEntry (s : MachineState) : MachineState :=
  (checkerRecordReadyState s).setPC ((checkerRecordReadyState s).pc+4)

theorem checker_record_parse_entry_eq (s : MachineState) : checkerRecordParseEntry s=
    (checkerRecordReadyState s).setPC ((checkerRecordReadyState s).pc+4) := by
  rw [checkerRecordParseEntry]

theorem checker_record_parse_entry_source (s : MachineState) :
    (checkerRecordParseEntry s).getReg .x20=s.getReg .x18+479 := by
  rw [checker_record_parse_entry_eq,MachineState.getReg_setPC,checker_record_ready_source]

theorem checker_record_parse_entry_metadata (s : MachineState) :
    (checkerRecordParseEntry s).getReg .x21=s.getReg .x8 := by
  rw [checker_record_parse_entry_eq,MachineState.getReg_setPC,checker_record_ready_metadata]

theorem checker_record_parse_entry_count (s : MachineState) :
    (checkerRecordParseEntry s).getReg .x22=17#64 := by
  rw [checker_record_parse_entry_eq,MachineState.getReg_setPC,checker_record_ready_count]

theorem checker_record_parse_entry_end (s : MachineState) :
    (checkerRecordParseEntry s).getReg .x19=(checkerRecordParseEntry s).getReg .x20+3 := by
  simpa only [checker_record_parse_entry_eq,MachineState.getReg_setPC] using checker_record_ready_end s

theorem checker_record_parse_entry_buffer (s : MachineState) : TailParseBuffer (checkerRecordParseEntry s) [] := by
  have buffer := checker_record_ready_buffer s
  constructor
  · rw [checker_record_parse_entry_eq,MachineState.getReg_setPC]; exact buffer.value
  · rw [checker_record_parse_entry_eq,MachineState.getReg_setPC]; exact buffer.count
  · exact buffer.pending

theorem checker_record_parse_entry_widths (s : MachineState) :
    ParseWidthsAt (checkerRecordParseEntry s) ((checkerRecordParseEntry s).getReg .x21)
      (InteriorCodec.recordSpec.map Prod.snd) := by
  rw [checker_record_parse_entry_eq]
  exact checker_record_ready_widths s

theorem checker_record_parse_entry_input (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    ParseInputAt (checkerRecordParseEntry s) ((checkerRecordParseEntry s).getReg .x20) input 17 := by
  rw [checker_record_parse_entry_eq]
  exact checker_record_ready_input s source input pointer metadata sourceEnd memory

theorem checker_record_parse_entry_apart (s : MachineState) (source : Nat)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) :
    TailApart ((checkerRecordParseEntry s).getReg .x21) ((checkerRecordParseEntry s).getReg .x20)
      ((InteriorCodec.recordSpec.map Prod.snd).map fun _ => []) := by
  rw [checker_record_parse_entry_metadata,checker_record_parse_entry_source,pointer,metadata]
  change TailApart (BitVec.ofNat 64 checkingMetadataBase)
    (BitVec.ofNat 64 source+BitVec.ofNat 64 479) _
  rw [←BitVec.ofNat_add]
  apply tail_apart_of_ranges
  · have order : checkingRawBase<checkingMetadataBase := by decide +kernel
    have count : ((InteriorCodec.recordSpec.map Prod.snd).map fun _ => ([] : List Bool)).length=17 := by decide +kernel
    rw [count]
    omega
  · decide +kernel

theorem checker_record_parser_ready (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase)
    (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    TailParsedFieldsReady 17 (checkerRecordParseEntry s) := by
  have count : (InteriorCodec.recordSpec.map Prod.snd).length=17 := by decide +kernel
  have sourceRoom : checkingMetadataBase+2*(InteriorCodec.recordSpec.map Prod.snd).length≤MEMORY_BYTES := by decide +kernel
  have inputRoom : source+479+(InteriorCodec.recordSpec.map Prod.snd).length+1≤MEMORY_BYTES := by
    have rawRoom : checkingRawBase≤MEMORY_BYTES := by decide +kernel
    rw [count]
    omega
  have inputPointer : (checkerRecordParseEntry s).getReg .x20=BitVec.ofNat 64 (source+479) := by
    rw [checker_record_parse_entry_source,pointer,BitVec.ofNat_add]
    rfl
  have result := tail_parsed_rows_access (InteriorCodec.recordSpec.map Prod.snd) [] input
    (checkerRecordParseEntry s) checkingMetadataBase (source+479)
    (checker_record_parse_entry_buffer s) byteSize
    (by intro width member; obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member; exact record_fields_small field belongs)
    (checker_record_parse_entry_widths s)
    (by rw [count]; exact checker_record_parse_entry_input s source input pointer metadata sourceEnd memory)
    (checker_record_parse_entry_apart s source pointer metadata sourceEnd)
    (by rw [checker_record_parse_entry_metadata]; exact metadata) inputPointer
    (by rw [count]; exact checker_record_parse_entry_count s) sourceRoom inputRoom
  rwa [count] at result

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual record parser entry, traversal and strict validation through word 136. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordParsedState (s : MachineState) : MachineState :=
  tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3

@[irreducible] def checkerRecordParserCycles (s : MachineState) : Nat :=
  tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+4

theorem checker_record_parsed_eq (s : MachineState) : checkerRecordParsedState s=
    tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3 := by
  rw [checkerRecordParsedState]

theorem checker_record_parser_cycles_eq (s : MachineState) : checkerRecordParserCycles s=
    tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+4 := by
  rw [checkerRecordParserCycles]

theorem checker_record_parser_cycles_bound (s : MachineState) : checkerRecordParserCycles s≤293 := by
  rw [checker_record_parser_cycles_eq]
  have bound := tail_parsed_fields_bound 17 (checkerRecordParseEntry s)
  omega

theorem checker_record_parse_entry_pc (s : MachineState) (pc : s.pc=4096+4*57) :
    (checkerRecordParseEntry s).pc=(4096+4*115)+4 := by
  rw [checker_record_parse_entry_eq]
  change (checkerRecordReadyState s).pc+4=_
  rw [checker_record_ready_pc s pc]

theorem checker_record_parser_enter (s : MachineState) (pc : s.pc=4096+4*57)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) (checkerRecordReadyState s) coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRecordParseEntry s) coins
          return result.charge 1 0) := by
  have fetched : fetch chainedCheckerImage (checkerRecordReadyState s)=some (.base (.BEQ .x22 .x0 72)) := by
    exact chained_checker_ops_at 115 (by rw [chained_checker_ops_length]; decide) _ (checker_record_ready_pc s pc)
  have skipped : ordinaryStep (checkerRecordReadyState s) (.base (.BEQ .x22 .x0 72))=
      some (checkerRecordParseEntry s) := by
    change some (execInstrBr (checkerRecordReadyState s) (.BEQ .x22 .x0 72))=_
    rw [checker_record_parse_entry_eq]
    congr 1
    change (if (checkerRecordReadyState s).getReg .x22 == (checkerRecordReadyState s).getReg .x0 then _ else _)=_
    rw [checker_record_ready_count]
    rfl
  rw [show 1+fuel=fuel+1 by omega]
  conv_lhs => rw [execute,fetched]
  simp only [skipped]
  rfl

theorem checker_record_parser_execution (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerRecordParserCycles s+fuel) (checkerRecordReadyState s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordParsedState s) coins
          return result.charge (checkerRecordParserCycles s) 0) := by
  have ready := checker_record_parser_ready s source input pointer metadata sourceEnd byteSize memory
  have entryPC : (checkerRecordParseEntry s).pc=
      if 17=0 then (4096+4*115)+72 else (4096+4*115)+4 := by
    exact checker_record_parse_entry_pc s pc
  rw [checking_manifest_image,checker_record_parser_cycles_eq,
    show tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+4+fuel=
      1+(tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+3+fuel) by omega,
    checker_record_parser_enter s pc,
    tail_parsed_fields_validate_execution chainedCheckerImage _ chained_checker_record_parse_at
      17 (checkerRecordParseEntry s) entryPC ready,←checker_record_parsed_eq]
  have arithmetic (cycles : Nat) :
      1+(tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+(3+cycles))=
        tailParsedFieldsCycles 17 (checkerRecordParseEntry s)+(4+cycles) := by omega
  simp [Execution.charge,Nat.add_assoc,arithmetic]

theorem checker_record_parsed_pc (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    (checkerRecordParsedState s).pc=4096+4*136 := by
  rw [checker_record_parsed_eq]
  exact tail_parsed_fields_validate_pc 17 (checkerRecordParseEntry s) (4096+4*115)
    (checker_record_parse_entry_pc s pc)
    (checker_record_parser_ready s source input pointer metadata sourceEnd byteSize memory)

theorem checker_record_initialization_parse (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (58+checkerRecordParserCycles s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordParsedState s) coins
          return result.charge (58+checkerRecordParserCycles s) 0) := by
  rw [Nat.add_assoc,checker_record_ready_execution s pc metadata,
    checker_record_parser_execution s source input pc pointer metadata sourceEnd byteSize memory]
  simp [Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual record parser flags and descriptor bytes imply strict codec acceptance. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

def checkerRecordParsedPayload (proof : Proof) (input : Nat → List Bool) : InteriorCodec.Record :=
  fieldsFromRows InteriorCodec.recordSpec (unpackBits (lowCount InteriorCodec.recordSpec) proof)
    (tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] input).fields

theorem checker_record_parsed_descriptor (s : MachineState) (source : Nat) (proof : Proof) (input : Nat → List Bool)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    BytesAt (checkerRecordParsedState s) (BitVec.ofNat 64 checkingMetadataBase)
      (descriptorBytes (highRows (checkerRecordParsedPayload proof input))) := by
  have result := parsed_payload_descriptor InteriorCodec.recordSpec proof input (checkerRecordParseEntry s)
    (checker_record_parse_entry_buffer s) byteSize record_fields_small
    (checker_record_parse_entry_widths s)
    (by exact checker_record_parse_entry_input s source input pointer metadata sourceEnd memory)
    (checker_record_parse_entry_apart s source pointer metadata sourceEnd) (by decide +kernel)
  change BytesAt (tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3)
    ((checkerRecordParseEntry s).getReg .x21) (descriptorBytes (highRows (checkerRecordParsedPayload proof input))) at result
  rw [checker_record_parse_entry_metadata,metadata,←checker_record_parsed_eq] at result
  exact result

theorem checker_record_parsed_accepts (s : MachineState) (source : Nat) (proof : Proof) (input : Nat → List Bool)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17)
    (length : proof.length=482)
    (tailSource : ∀ index, index<(proof.drop 479).length → input index=byteBits ((proof.drop 479).getD index 0))
    (accepted : (checkerRecordParsedState s).getReg .x24=1#64) :
    unpack InteriorCodec.recordSpec proof=some (checkerRecordParsedPayload proof input) ∧
      decode InteriorCodec.recordSpec proof=checkerRecordParsedPayload proof input := by
  have tailLength : (proof.drop (lowCount InteriorCodec.recordSpec/8)).length=3 := by
    rw [InteriorCodec.record_counts.1,List.length_drop,length]
  have result := parsed_payload_accepts InteriorCodec.recordSpec proof input (checkerRecordParseEntry s)
    (checker_record_parse_entry_buffer s) byteSize (by decide +kernel) record_fields_small
    (by rw [InteriorCodec.record_counts.1,length]; decide)
    (checker_record_parse_entry_widths s)
    (checker_record_parse_entry_input s source input pointer metadata sourceEnd memory)
    (checker_record_parse_entry_apart s source pointer metadata sourceEnd) (by decide +kernel)
    (by rw [tailLength]; decide)
    (by rw [tailLength]; exact checker_record_parse_entry_end s)
    (by simpa only [InteriorCodec.record_counts.1] using tailSource)
  apply result
  change (tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3).getReg .x24=1#64
  rwa [←checker_record_parsed_eq]

theorem checker_record_parsed_flag (s : MachineState) (source : Nat) (input : Nat → List Bool)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (byteSize : ∀ index, (input index).length=8)
    (memory : ParseInputAt s (s.getReg .x18+479) input 17) :
    let plan := tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] input
    (checkerRecordParsedState s).getReg .x24=(if plan.read=3 ∧
      (∀ index, index<plan.carry.length → plan.carry.getD index false=false) then 1#64 else 0#64) := by
  have result := native_tail_parse_result (InteriorCodec.recordSpec.map Prod.snd) [] input
    (checkerRecordParseEntry s) (checker_record_parse_entry_buffer s) byteSize
    (by intro width member; obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member; exact record_fields_small field belongs)
    (checker_record_parse_entry_widths s)
    (checker_record_parse_entry_input s source input pointer metadata sourceEnd memory)
    (checker_record_parse_entry_apart s source pointer metadata sourceEnd) (by decide +kernel)
    3 (by decide) (checker_record_parse_entry_end s)
  simpa only [checker_record_parsed_eq,
    show (InteriorCodec.recordSpec.map Prod.snd).length=17 from by decide +kernel] using result.1

end CommitGolfCandidate.Chained.Native

end

section

/-! Read parser bytes from actual entry memory and preserve the encoded record. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

def checkerRecordInput (s : MachineState) (index : Nat) : List Bool :=
  byteBits (s.getByte ((s.getReg .x18+479)+BitVec.ofNat 64 index))

theorem checker_record_input_size (s : MachineState) (index : Nat) :
    (checkerRecordInput s index).length=8 := byte_bits_length _

theorem checker_record_input_memory (s : MachineState) :
    ParseInputAt s (s.getReg .x18+479) (checkerRecordInput s) 17 := by
  intro index inside
  exact (byte_bits_word _).symm

theorem checker_record_input_tail (s : MachineState) (proof : Proof) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) (index : Nat) (inside : index<(proof.drop 479).length) :
    checkerRecordInput s index=byteBits ((proof.drop 479).getD index 0) := by
  have bounded : 479+index<proof.length := by simp only [List.length_drop,length] at inside ⊢; omega
  unfold checkerRecordInput
  change byteBits (s.getByte ((s.getReg .x18+BitVec.ofNat 64 479)+BitVec.ofNat 64 index))=_
  rw [byte_offset_add,memory _ bounded]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_drop]

theorem checker_record_plan_complete (input : Nat → List Bool) (byteSize : ∀ index, (input index).length=8) :
    let plan := tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] input
    plan.read=3 ∧ plan.carry=[] := by
  have small : ∀ width ∈ InteriorCodec.recordSpec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact record_fields_small field belongs
  have sum : (InteriorCodec.recordSpec.map Prod.snd).sum=24 := by decide +kernel
  have read := inverse_plan_read_exact (InteriorCodec.recordSpec.map Prod.snd) input byteSize small
  rw [sum] at read
  have shape := tail_parse_plan_widths (InteriorCodec.recordSpec.map Prod.snd) [] input byteSize small
  have fields : (tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] input).fields.flatten.length=24 := by
    rw [List.length_flatten,shape,sum]
  have bits := congrArg List.length (tail_parse_plan_bits (InteriorCodec.recordSpec.map Prod.snd) [] input)
  simp only [List.length_append,List.nil_append,pull_bit_bytes_length _ _ byteSize,fields,read] at bits
  refine ⟨read,?_⟩
  cases empty : (tailParsePlan (InteriorCodec.recordSpec.map Prod.snd) [] input).carry with
  | nil => rfl
  | cons bit rest => simp only [empty,List.length_cons] at bits; omega

theorem checker_record_parser_accepts_all (s : MachineState) (source : Nat)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) :
    (checkerRecordParsedState s).getReg .x24=1#64 := by
  have result := checker_record_parsed_flag s source (checkerRecordInput s) pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s)
  have complete := checker_record_plan_complete (checkerRecordInput s) (checker_record_input_size s)
  dsimp only at result complete
  rw [complete.1,complete.2] at result
  simpa using result

theorem checker_record_source_decodes (s : MachineState) (source : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) :
    unpack InteriorCodec.recordSpec proof=some (checkerRecordParsedPayload proof (checkerRecordInput s)) ∧
      BytesAt (checkerRecordParsedState s) (BitVec.ofNat 64 checkingMetadataBase)
        (descriptorBytes (highRows (checkerRecordParsedPayload proof (checkerRecordInput s)))) := by
  refine ⟨?_,checker_record_parsed_descriptor s source proof (checkerRecordInput s) pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s)⟩
  exact (checker_record_parsed_accepts s source proof (checkerRecordInput s) pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s) length
    (checker_record_input_tail s proof length memory)
    (checker_record_parser_accepts_all s source pointer metadata sourceEnd)).1

theorem checker_record_parsed_source (s : MachineState) (source : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) :
    BytesAt (checkerRecordParsedState s) (s.getReg .x18) proof := by
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
  have ordering : checkingRawBase<checkingMetadataBase := by decide +kernel
  have room := checking_metadata_room
  intro index inside
  have bounded : index<482 := by rwa [length] at inside
  rw [checker_record_parsed_eq]
  have same := result.2 (s.getReg .x18+BitVec.ofNat 64 index)
  change (tailValidatePrefix (tailParsedFieldsState 17 (checkerRecordParseEntry s)) 3).getByte _=_ at same
  rw [same,write_parsed_rows_preserves]
  · rw [checker_record_parse_entry_eq]
    change (checkerRecordReadyState s).getByte _=_
    rw [checker_record_ready_memory]
    · exact memory index inside
    · intro row before
      rw [pointer,metadata,←BitVec.ofNat_add,←BitVec.ofNat_add]
      exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)
  · intro row before
    rw [rows] at before
    rw [checker_record_parse_entry_metadata,pointer,metadata,←BitVec.ofNat_add,←BitVec.ofNat_add]
    exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

end CommitGolfCandidate.Chained.Native

end

section

/-! Record parsing preserves raw-output, source, count and metadata control registers. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem checker_record_setup_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x19,.x20,.x21,.x22,.x23,.x25]) :
    (checkerRecordSetupState 6 s).getReg reg=s.getReg reg := by
  simp only [checker_record_setup_succ,checker_record_setup_zero]
  cases reg <;> simp at kept <;> rfl

theorem checker_record_ready_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x7,.x10,.x19,.x20,.x21,.x22,.x23,.x25]) :
    (checkerRecordReadyState s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_record_ready_eq,checker_record_setup_register _ _ (by decide),
    width_table_register recordWidths _ _ (by decide) (by decide)]
  all_goals rfl

theorem checker_record_parsed_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x7,.x10,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x28]) :
    (checkerRecordParsedState s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_record_parsed_eq,parsed_fields_register 17 _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    checker_record_parse_entry_eq,MachineState.getReg_setPC,
    checker_record_ready_register _ _ (by decide)]

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual record source/metadata reset and the two required raw padding stores. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerRecordPaddingOps : List Instr :=
  [.ADDI .x5 .x18 0,.ADDI .x7 .x8 0,.SB .x6 .x0 46,.SB .x6 .x0 47]

@[irreducible] def checkerRecordPaddingPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerRecordPaddingOps.take n).foldl execInstrBr s

theorem checker_record_padding_zero (s : MachineState) : checkerRecordPaddingPrefix s 0=s := by
  rw [checkerRecordPaddingPrefix]
  rfl

theorem checker_record_padding_succ (s : MachineState) (n : Nat) (small : n<4) :
    checkerRecordPaddingPrefix s (n+1)=
      execInstrBr (checkerRecordPaddingPrefix s n) (checkerRecordPaddingOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerRecordPaddingPrefix <;> rfl

theorem checker_record_padding_at : OpsAt chainedCheckerImage (4096+4*138) checkerRecordPaddingOps := by
  exact chained_checker_slice_at 138 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_record_padding_register (s : MachineState) (n : Nat) (small : n≤4) (reg : Reg)
    (kept : reg∉[.x5,.x7]) : (checkerRecordPaddingPrefix s n).getReg reg=s.getReg reg := by
  interval_cases n <;> unfold checkerRecordPaddingPrefix <;> cases reg <;> simp at kept <;> rfl

theorem checker_record_padding_source (s : MachineState) :
    (checkerRecordPaddingPrefix s 4).getReg .x5=s.getReg .x18 := by
  unfold checkerRecordPaddingPrefix
  exact BitVec.add_zero _

theorem checker_record_padding_metadata (s : MachineState) :
    (checkerRecordPaddingPrefix s 4).getReg .x7=s.getReg .x8 := by
  unfold checkerRecordPaddingPrefix
  exact BitVec.add_zero _

theorem checker_record_padding_byte (s : MachineState) (query : Word) :
    (checkerRecordPaddingPrefix s 4).getByte query=
      if query=s.getReg .x6+47 then 0 else if query=s.getReg .x6+46 then 0 else s.getByte query := by
  unfold checkerRecordPaddingPrefix
  change ((s.setByte (s.getReg .x6+46) 0).setByte (s.getReg .x6+47) 0).getByte query=_
  simp only [CommitGolfCandidate.set_byte_read]

theorem checker_record_padding_bytes (s : MachineState) :
    BytesAt (checkerRecordPaddingPrefix s 4) (s.getReg .x6+46) [0,0] := by
  intro index inside
  have bounded : index<2 := by simpa using inside
  interval_cases index
  · rw [checker_record_padding_byte]
    simp
  · have location : (s.getReg .x6+46)+BitVec.ofNat 64 1=s.getReg .x6+47 := by rw [BitVec.add_assoc]; rfl
    rw [location,checker_record_padding_byte]
    simp

theorem checker_record_padding_pc (s : MachineState) (n : Nat) (small : n≤4) :
    (checkerRecordPaddingPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> unfold checkerRecordPaddingPrefix
  · exact (BitVec.add_zero _).symm
  · rfl
  · change (s.pc+4)+4=s.pc+8
    rw [BitVec.add_assoc]; rfl
  · change ((s.pc+4)+4)+4=s.pc+12
    rw [BitVec.add_assoc,BitVec.add_assoc]; rfl
  · change (((s.pc+4)+4)+4)+4=s.pc+16
    rw [BitVec.add_assoc,BitVec.add_assoc,BitVec.add_assoc]; rfl

theorem checker_record_padding_execution (s : MachineState) (outputBase : Nat)
    (pc : s.pc=4096+4*138) (pointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (room : outputBase+48≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRecordPaddingPrefix s 4) coins
          return result.charge 4 0) := by
  have numeric : (s.getReg .x6).toNat=outputBase := by
    rw [pointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    unfold MEMORY_BYTES at room
    omega
  have left := byte_access_offset (s.getReg .x6) 46 (by rw [numeric]; omega)
  have right := byte_access_offset (s.getReg .x6) 47 (by rw [numeric]; omega)
  conv_lhs => rw [←checker_record_padding_zero s]
  apply execute_unit_steps (states := checkerRecordPaddingPrefix s)
  intro i inside
  refine ⟨.base (checkerRecordPaddingOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_record_padding_at i (by change i<4; exact inside)
    rw [checker_record_padding_pc s i (by omega),pc]
  · rw [checker_record_padding_succ s i inside]
    interval_cases i
    · rfl
    · rfl
    · have valid : memoryArgumentsValid (checkerRecordPaddingPrefix s 2) (.SB .x6 .x0 46)=true := by
        change accessValid ((checkerRecordPaddingPrefix s 2).getReg .x6+46) 1=true
        rw [checker_record_padding_register s 2 (by decide) .x6 (by decide)]
        exact left
      change ordinaryStep _ (.base (.SB .x6 .x0 46))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
    · have valid : memoryArgumentsValid (checkerRecordPaddingPrefix s 3) (.SB .x6 .x0 47)=true := by
        change accessValid ((checkerRecordPaddingPrefix s 3).getReg .x6+47) 1=true
        rw [checker_record_padding_register s 3 (by decide) .x6 (by decide)]
        exact right
      change ordinaryStep _ (.base (.SB .x6 .x0 47))=_
      simp only [ordinaryStep,valid,↓reduceIte]
      rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Chained.Native

end

section

/-! The two concrete zero stores initialize every raw-record padding byte. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem payload_raw_padding_nil {spec : Spec} (payload : Payload spec)
    (small : ∀ field ∈ spec, field.2≤6) (s : MachineState) (base : Word) :
    RawPaddingAt s base (payloadRawFields payload [] small (by simp)) := by
  induction payload generalizing base with
  | nil => trivial
  | @cons low high spec value rest ih =>
    constructor
    · intro index inside
      simp at inside
    · exact ih _ _

theorem payload_record_raw_padding_at {spec : Spec} (record : Payload ((120,1)::(232,6)::spec))
    (small : ∀ field ∈ (120,1)::(232,6)::spec, field.2≤6) (s : MachineState) (base : Word)
    (padding : BytesAt s (base+46) [0,0]) :
    RawPaddingAt s base (payloadRawFields record [[],[0,0]] small (by simp)) := by
  cases record with
  | cons nonce rest =>
    cases rest with
    | cons leaf parents =>
      rw [payloadRawFields,RawPaddingAt,payloadRawFields,RawPaddingAt]
      refine ⟨?_,?_,payload_raw_padding_nil parents _ s _⟩
      · intro index inside
        simp at inside
      · simp only [RawField.bytes,List.length_append,List.length_cons,List.length_nil,
          packed_bits_length,List.length_ofFn]
        change BytesAt s ((base+16)+30) [0,0]
        rw [BitVec.add_assoc]
        exact padding

theorem record_raw_padding_at (record : InteriorCodec.Record) (s : MachineState) (base : Word)
    (padding : BytesAt s (base+46) [0,0]) : RawPaddingAt s base (recordRawFields record) :=
  payload_record_raw_padding_at record record_fields_small s base padding

theorem checker_record_padding_ready (record : InteriorCodec.Record) (s : MachineState) :
    RawPaddingAt (checkerRecordPaddingPrefix s 4) (s.getReg .x6) (recordRawFields record) :=
  record_raw_padding_at record _ _ (checker_record_padding_bytes s)

end CommitGolfCandidate.Chained.Native

end

section

/-! Compose the actual accepted-record branch and raw reconstruction setup. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordReconstructionEntry (s : MachineState) : MachineState :=
  checkerRecordPaddingPrefix ((checkerRecordParsedState s).setPC ((checkerRecordParsedState s).pc+8)) 4

theorem checker_record_reconstruction_entry_eq (s : MachineState) : checkerRecordReconstructionEntry s=
    checkerRecordPaddingPrefix ((checkerRecordParsedState s).setPC ((checkerRecordParsedState s).pc+8)) 4 := by
  rw [checkerRecordReconstructionEntry]

theorem checker_record_reconstruction_source (s : MachineState) :
    (checkerRecordReconstructionEntry s).getReg .x5=s.getReg .x18 := by
  rw [checker_record_reconstruction_entry_eq,checker_record_padding_source,MachineState.getReg_setPC,
    checker_record_parsed_register s .x18 (by decide)]

theorem checker_record_reconstruction_metadata (s : MachineState) :
    (checkerRecordReconstructionEntry s).getReg .x7=s.getReg .x8 := by
  rw [checker_record_reconstruction_entry_eq,checker_record_padding_metadata,MachineState.getReg_setPC,
    checker_record_parsed_register s .x8 (by decide)]

theorem checker_record_reconstruction_output (s : MachineState) :
    (checkerRecordReconstructionEntry s).getReg .x6=s.getReg .x6 := by
  rw [checker_record_reconstruction_entry_eq,checker_record_padding_register _ 4 (by decide) .x6 (by decide),
    MachineState.getReg_setPC,checker_record_parsed_register s .x6 (by decide)]

private theorem merged_ChainedCheckerRecordReconstructionEntry_reconstruction_byte_set_pc (s : MachineState) (target query : Word) :
    (s.setPC target).getByte query=s.getByte query := rfl

theorem checker_record_reconstruction_byte (s : MachineState) (query : Word) :
    (checkerRecordReconstructionEntry s).getByte query=
      if query=s.getReg .x6+47 then 0 else if query=s.getReg .x6+46 then 0 else (checkerRecordParsedState s).getByte query := by
  rw [checker_record_reconstruction_entry_eq,checker_record_padding_byte,MachineState.getReg_setPC,
    checker_record_parsed_register s .x6 (by decide)]
  rw [merged_ChainedCheckerRecordReconstructionEntry_reconstruction_byte_set_pc]

theorem checker_record_reconstruction_padding (s : MachineState) (record : InteriorCodec.Record) :
    RawPaddingAt (checkerRecordReconstructionEntry s) (s.getReg .x6) (recordRawFields record) := by
  have padding := checker_record_padding_ready record
    ((checkerRecordParsedState s).setPC ((checkerRecordParsedState s).pc+8))
  rw [MachineState.getReg_setPC,checker_record_parsed_register s .x6 (by decide),
    ←checker_record_reconstruction_entry_eq] at padding
  exact padding

theorem checker_record_reconstruction_pc (s : MachineState) (source : Nat)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) :
    (checkerRecordReconstructionEntry s).pc=4096+4*142 := by
  rw [checker_record_reconstruction_entry_eq,checker_record_padding_pc _ 4 (by decide)]
  change ((checkerRecordParsedState s).pc+8)+16=_
  rw [checker_record_parsed_pc s source (checkerRecordInput s) pc pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s)]
  rfl

private theorem merged_ChainedCheckerRecordReconstructionEntry_accepted_record_guard (s : MachineState) (pc : s.pc=4096+4*136)
    (accepted : s.getReg .x24=1#64) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (1+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (s.setPC (s.pc+8)) coins
          return result.charge 1 0) := by
  have fetched : fetch chainedCheckerImage s=some (.base (.BNE .x24 .x0 8)) :=
    chained_checker_ops_at 136 (by rw [chained_checker_ops_length]; decide) s pc
  have step : ordinaryStep s (.base (.BNE .x24 .x0 8))=some (s.setPC (s.pc+8)) := by
    change some (if s.getReg .x24 != s.getReg .x0 then _ else _)=_
    rw [accepted]
    rfl
  rw [show 1+fuel=fuel+1 by omega]
  conv_lhs => rw [execute,fetched]
  simp only [step]
  rfl

theorem checker_record_reconstruction_entry_execution (s : MachineState) (source outputBase : Nat)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (room : outputBase+48≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) (checkerRecordParsedState s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordReconstructionEntry s) coins
          return result.charge 5 0) := by
  have parsedPC := checker_record_parsed_pc s source (checkerRecordInput s) pc pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s)
  have guardedPC : ((checkerRecordParsedState s).setPC ((checkerRecordParsedState s).pc+8)).pc=4096+4*138 := by
    change (checkerRecordParsedState s).pc+8=_
    rw [parsedPC]
    rfl
  have guardedPointer : ((checkerRecordParsedState s).setPC ((checkerRecordParsedState s).pc+8)).getReg .x6=
      BitVec.ofNat 64 outputBase := by
    rw [MachineState.getReg_setPC,checker_record_parsed_register s .x6 (by decide)]
    exact outputPointer
  rw [checking_manifest_image,show 5+fuel=1+(4+fuel) by omega,
    merged_ChainedCheckerRecordReconstructionEntry_accepted_record_guard _ parsedPC (checker_record_parser_accepts_all s source pointer metadata sourceEnd),
    checker_record_padding_execution _ outputBase guardedPC guardedPointer room,←checker_record_reconstruction_entry_eq]
  simp [Execution.charge,←Nat.add_assoc]

theorem checker_record_initialization_reconstruction (s : MachineState) (source outputBase : Nat)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (room : outputBase+48≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (58+checkerRecordParserCycles s+5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordReconstructionEntry s) coins
          return result.charge (58+checkerRecordParserCycles s+5) 0) := by
  rw [show 58+checkerRecordParserCycles s+5+fuel=(58+checkerRecordParserCycles s)+(5+fuel) by omega,
    checker_record_initialization_parse s source (checkerRecordInput s) pc pointer metadata sourceEnd
      (checker_record_input_size s) (checker_record_input_memory s),
    checker_record_reconstruction_entry_execution s source outputBase pc pointer metadata sourceEnd outputPointer room]
  simp [Execution.charge,Nat.add_assoc]

theorem checker_record_initialization_reconstruction_bound (s : MachineState) :
    58+checkerRecordParserCycles s+5≤356 := by
  have bound := checker_record_parser_cycles_bound s
  omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Actual word-142 memory and pointer invariants discharge inverse-record readiness. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem checker_record_low_body (s : MachineState) (proof : Proof) (length : proof.length=482) :
    lowBytes (checkerRecordParsedPayload proof (checkerRecordInput s))=proof.take 479 := by
  have widths := tail_parse_plan_widths (InteriorCodec.recordSpec.map Prod.snd) [] (checkerRecordInput s)
    (checker_record_input_size s) (by
      intro width member
      obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
      exact record_fields_small field belongs)
  exact low_bytes_from_rows InteriorCodec.recordSpec proof _ widths (by decide +kernel)
    (by rw [InteriorCodec.record_counts.1,length]; decide)

private theorem merged_ChainedCheckerRecordInverseReady_reconstruction_byte_away (s : MachineState) (query : Word)
    (left : query≠s.getReg .x6+46) (right : query≠s.getReg .x6+47) :
    (checkerRecordReconstructionEntry s).getByte query=(checkerRecordParsedState s).getByte query := by
  rw [checker_record_reconstruction_byte,ite_eq_right right,ite_eq_right left]

theorem checker_record_inverse_source (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) :
    BytesAt (checkerRecordReconstructionEntry s) (BitVec.ofNat 64 source) proof := by
  have original := checker_record_parsed_source s source proof pointer metadata sourceEnd length memory
  have room := checking_metadata_room
  intro index inside
  have bound : index<482 := by rwa [length] at inside
  rw [merged_ChainedCheckerRecordInverseReady_reconstruction_byte_away]
  · rw [←pointer]
    exact original index inside
  all_goals rw [outputPointer,←BitVec.ofNat_add]
  all_goals first
    | change BitVec.ofNat 64 (source+index)≠BitVec.ofNat 64 outputBase+BitVec.ofNat 64 46
    | change BitVec.ofNat 64 (source+index)≠BitVec.ofNat 64 outputBase+BitVec.ofNat 64 47
  all_goals rw [←BitVec.ofNat_add]
  all_goals exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_record_inverse_table (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) :
    BytesAt (checkerRecordReconstructionEntry s) (BitVec.ofNat 64 checkingMetadataBase)
      (descriptorBytes (highRows (checkerRecordParsedPayload proof (checkerRecordInput s)))) := by
  have original := checker_record_parsed_descriptor s source proof (checkerRecordInput s) pointer metadata sourceEnd
    (checker_record_input_size s) (checker_record_input_memory s)
  have room := checking_metadata_room
  intro index inside
  have bound : index<34 := by rwa [(record_descriptor_sizes _).2.2] at inside
  rw [merged_ChainedCheckerRecordInverseReady_reconstruction_byte_away]
  · exact original index inside
  all_goals rw [outputPointer,←BitVec.ofNat_add]
  all_goals first
    | change BitVec.ofNat 64 (checkingMetadataBase+index)≠BitVec.ofNat 64 outputBase+BitVec.ofNat 64 46
    | change BitVec.ofNat 64 (checkingMetadataBase+index)≠BitVec.ofNat 64 outputBase+BitVec.ofNat 64 47
  all_goals rw [←BitVec.ofNat_add]
  all_goals exact word_of_nat_ne _ _ (by omega) (by omega) (by omega)

theorem checker_record_inverse_ready (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) :
    InverseFieldsReady (recordRawFields (checkerRecordParsedPayload proof (checkerRecordInput s))) [] []
      (checkerRecordReconstructionEntry s) source outputBase checkingMetadataBase := by
  let record := checkerRecordParsedPayload proof (checkerRecordInput s)
  have low : rawFieldsLow (recordRawFields record)=lowBytes record :=
    payload_raw_fields_low record recordSourcePads record_fields_small record_pads_small
  have high : rawFieldsMeta (recordRawFields record)=descriptorBytes (highRows record) := by
    rw [recordRawFields,raw_fields_meta_rows,payload_raw_fields_high]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [checker_record_reconstruction_source,pointer]
  · simpa only [List.length_nil,Nat.add_zero,checker_record_reconstruction_output] using outputPointer
  · rw [checker_record_reconstruction_metadata,metadata]
  · rw [low,List.append_nil,checker_record_low_body s proof length]
    have original := checker_record_inverse_source s source outputBase proof pointer metadata sourceEnd outputStart
      outputPointer outputEnd length memory
    intro index inside
    have bound : index<proof.length := by
      rw [List.length_take] at inside
      omega
    rw [original index bound]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take]
    rw [ite_eq_left (by rw [List.length_take] at inside; omega)]
  · intro index inside
    simp at inside
  · rw [high]
    exact checker_record_inverse_table s source outputBase proof pointer metadata sourceEnd outputPointer outputEnd
  · simpa only [List.length_nil,Nat.add_zero,outputPointer] using checker_record_reconstruction_padding s record
  · rw [low,(record_descriptor_sizes record).1,List.length_nil,Nat.add_zero]
    omega
  · simpa only [List.length_nil,Nat.add_zero,record_raw_fields_length] using outputEnd
  · rw [record_raw_fields_count]
    have room := checking_metadata_room
    omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Exact installed inverse-body execution, reconstructed record and cursor advances. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def checkerRecordReconstructedState (s : MachineState) (proof : Proof) : MachineState :=
  inverseRawFieldsState (recordRawFields (checkerRecordParsedPayload proof (checkerRecordInput s)))
    (checkerRecordReconstructionEntry s)

theorem checker_record_reconstructed_eq (s : MachineState) (proof : Proof) :
    checkerRecordReconstructedState s proof=
      inverseRawFieldsState (recordRawFields (checkerRecordParsedPayload proof (checkerRecordInput s)))
        (checkerRecordReconstructionEntry s) := by
  rw [checkerRecordReconstructedState]

theorem inverse_raw_fields_pc (fields : List RawField) (s : MachineState) :
    (inverseRawFieldsState fields s).pc=s.pc+BitVec.ofNat 64 (4*inverseRawFieldsSteps fields) := by
  induction fields generalizing s with
  | nil => rw [inverse_raw_fields_zero]; exact (BitVec.add_zero _).symm
  | cons field fields ih =>
    rw [inverse_raw_fields_cons,ih,inverse_raw_field_pc,byte_offset_add]
    congr 2
    change 4*inverseRawFieldSteps field+4*inverseRawFieldsSteps fields=
      4*(inverseRawFieldSteps field+inverseRawFieldsSteps fields)
    omega

theorem checker_record_inverse_fields_at (record : InteriorCodec.Record) :
    InverseRawFieldsAt chainedCheckerImage (4096+4*142) (recordRawFields record) := by
  apply inverse_raw_fields_at_of_ops
  rw [inverse_record_raw_fields_ops]
  exact chained_checker_record_inverse_at

theorem checker_record_inverse_execution (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2018+fuel) (checkerRecordReconstructionEntry s) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordReconstructedState s proof) coins
          return result.charge 2018 0) := by
  have ready := checker_record_inverse_ready s source outputBase proof pointer metadata sourceEnd outputStart
    outputPointer outputEnd length memory
  have result := inverse_raw_fields_execution chainedCheckerImage _ [] [] _ source outputBase checkingMetadataBase
    (4096+4*142) (checker_record_inverse_fields_at _) ready
    (checker_record_reconstruction_pc s source pc pointer metadata sourceEnd)
    (by rw [record_raw_fields_count]; decide +kernel) fuel coins
  simpa only [checking_manifest_image,checker_record_reconstructed_eq,inverse_record_steps] using result

theorem inverse_record_content (record : InteriorCodec.Record) (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady (recordRawFields record) [] [] s source outputBase metadata) :
    BytesAt (inverseRawFieldsState (recordRawFields record) s) (BitVec.ofNat 64 outputBase)
      (rawFieldsBytes (recordRawFields record)) ∧
    (inverseRawFieldsState (recordRawFields record) s).getReg .x5=BitVec.ofNat 64 (source+479) ∧
    (inverseRawFieldsState (recordRawFields record) s).getReg .x6=BitVec.ofNat 64 (outputBase+498) ∧
    (inverseRawFieldsState (recordRawFields record) s).getReg .x7=BitVec.ofNat 64 (metadata+34) := by
  have result := inverse_raw_fields_memory _ [] [] s source outputBase metadata ready
  have low : rawFieldsLow (recordRawFields record)=lowBytes record :=
    payload_raw_fields_low record recordSourcePads record_fields_small record_pads_small
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [List.nil_append] using result.output
  · simpa only [low,(record_descriptor_sizes record).1] using result.sourcePointer
  · simpa only [List.nil_append,record_raw_fields_length] using result.outputPointer
  · simpa only [record_raw_fields_count] using result.metaPointer

theorem checker_record_reconstructed_content (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) :
    let record := checkerRecordParsedPayload proof (checkerRecordInput s)
    BytesAt (checkerRecordReconstructedState s proof) (BitVec.ofNat 64 outputBase) (rawFieldsBytes (recordRawFields record)) ∧
    (checkerRecordReconstructedState s proof).getReg .x5=BitVec.ofNat 64 (source+479) ∧
    (checkerRecordReconstructedState s proof).getReg .x6=BitVec.ofNat 64 (outputBase+498) ∧
    (checkerRecordReconstructedState s proof).getReg .x7=BitVec.ofNat 64 (checkingMetadataBase+34) := by
  have ready := checker_record_inverse_ready s source outputBase proof pointer metadata sourceEnd outputStart
    outputPointer outputEnd length memory
  simpa only [checker_record_reconstructed_eq] using
    inverse_record_content _ _ source outputBase checkingMetadataBase ready

theorem checker_record_reconstructed_pc (s : MachineState) (source : Nat) (proof : Proof)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) :
    (checkerRecordReconstructedState s proof).pc=4096+4*2160 := by
  rw [checker_record_reconstructed_eq,inverse_raw_fields_pc,inverse_record_steps,
    checker_record_reconstruction_pc s source pc pointer metadata sourceEnd]
  rfl

theorem checker_record_initialization_inverse (s : MachineState) (source outputBase : Nat) (proof : Proof)
    (pc : s.pc=4096+4*57) (pointer : s.getReg .x18=BitVec.ofNat 64 source)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (sourceEnd : source+497<checkingRawBase) (outputStart : checkingRawBase≤outputBase)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 outputBase)
    (outputEnd : outputBase+498≤checkingMetadataBase) (length : proof.length=482)
    (memory : BytesAt s (s.getReg .x18) proof) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (58+checkerRecordParserCycles s+5+2018+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordReconstructedState s proof) coins
          return result.charge (58+checkerRecordParserCycles s+5+2018) 0) := by
  have room : outputBase+48≤MEMORY_BYTES := by
    have metaRoom : checkingMetadataBase+34≤MEMORY_BYTES := by decide +kernel
    omega
  rw [show 58+checkerRecordParserCycles s+5+2018+fuel=
      (58+checkerRecordParserCycles s+5)+(2018+fuel) by omega,
    checker_record_initialization_reconstruction s source outputBase pc pointer metadata sourceEnd outputPointer room,
    checker_record_inverse_execution s source outputBase proof pc pointer metadata sourceEnd outputStart outputPointer outputEnd length memory]
  have arithmetic (cycles : Nat) : 5+(2018+cycles)=2023+cycles := by omega
  simp [Execution.charge,Nat.add_assoc,arithmetic]

theorem checker_record_initialization_inverse_bound (s : MachineState) :
    58+checkerRecordParserCycles s+5+2018≤2374 := by
  have bound := checker_record_initialization_reconstruction_bound s
  omega

end CommitGolfCandidate.Chained.Native

end
