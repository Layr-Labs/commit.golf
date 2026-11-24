import CommitGolfCandidate.ChainedFooterEntry

/-! Whole native record/footer postpass from canonical raw memory through halt. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem footer_encode_byte_bound (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    (encode footer).length≤30*nodes.length := by
  have bits : InteriorCodec.footerBits nodes≤238*nodes.length := by
    clear footer
    induction nodes with
    | nil => simp [InteriorCodec.footerBits]
    | cons node nodes ih =>
      have width : InteriorCodec.footerWidth node≤238 := by unfold InteriorCodec.footerWidth; split <;> omega
      simp only [InteriorCodec.footerBits,List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
      omega
  rw [InteriorCodec.encode_footer_length]
  omega

theorem native_packet_pack (groups : List Nat) (records : List InteriorCodec.Record)
    (footer : Payload (InteriorCodec.footerSpec (capFrontierNodes groups 1 8))) (suffix : Proof)
    (s : MachineState) (source output metadata : Nat)
    (ready : RecordStreamReady records
      (rawFieldsBytes (footerRawFields (capFrontierNodes groups 1 8) footer)++suffix) s source output metadata)
    (nonempty : records≠[]) (base : s.getReg .x17=BitVec.ofNat 64 output)
    (marks : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node)
    (above : 8192≤output) (metaAbove : 8192≤metadata)
    (capacity : metadata+2*(capFrontierNodes groups 1 8).length≤MEMORY_BYTES) :
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) s coins=pure ⟨.success,after,cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 output) (encodedRecords records++encode footer) ∧
      after.getReg .x6=BitVec.ofNat 64 (output+(encodedRecords records).length+(encode footer).length) ∧
      (after.getReg .x11).toNat=(encodedRecords records).length+(encode footer).length ∧
      cycles≤2273*records.length+66455+13*(capFrontierNodes groups 1 8).length := by
  let nodes := capFrontierNodes groups 1 8
  let raw := rawFieldsBytes (footerRawFields nodes footer)++suffix
  have footerCapacity : metadata+2*(footerRawFields nodes footer).length≤MEMORY_BYTES := by
    simpa only [footer_raw_fields_count] using capacity
  have entry := record_loop_footer_ready groups records (footerRawFields nodes footer) suffix s source output metadata
    ready base marks above metaAbove footerCapacity
  have complete := record_loop_ready records raw s source output metadata ready
  have endPC : (recordLoopState records s).pc=12380 := by simpa using complete.pc
  have footerPC : (footerInitPrefix (recordLoopState records s) 7).pc=12408 := by
    rw [footer_init_pc _ 7 (by decide),endPC]
    rfl
  have count : 0<records.length := by exact List.length_pos_iff_ne_nil.mpr nonempty
  have inputBound : source+498*records.length+30*nodes.length+suffix.length≤metadata := by
    have bound := ready.separate
    simpa only [raw,List.length_append,footer_raw_fields_length,Nat.add_assoc] using bound
  dsimp only [nodes] at inputBound
  have gap : output+(encodedRecords records).length+(lowBytes footer).length+nodes.length<metadata := by
    dsimp only [nodes]
    rw [encoded_records_length,footer_low_bytes_length]
    have ordered := ready.ordered
    omega
  have outputFit : output+(encodedRecords records).length+(encode footer).length<2^64 := by
    have encoded := footer_encode_byte_bound nodes footer
    rw [encoded_records_length]
    have ordered := ready.ordered
    have room := ready.capacity
    unfold MEMORY_BYTES at room
    omega
  obtain ⟨final,footerCycles,footerRun,footerBytes,footerOutput,footerLength,footerBound⟩ :=
    footer_complete groups footer suffix (encodedRecords records) _ (source+498*records.length) output metadata
      entry footerPC gap outputFit
  let cycles := recordLoopCycles records s+7+footerCycles
  refine ⟨final,cycles,?_,footerBytes,footerOutput,footerLength,?_⟩
  · intro fuel coins
    rw [show cycles+fuel=recordLoopCycles records s+(7+(footerCycles+fuel)) by dsimp only [cycles]; omega,
      record_loop_execution records raw s source output metadata ready,
      footer_init_execution _ endPC,footerRun fuel coins]
    simp only [pure_bind,Execution.charge]
    congr 2 <;> dsimp only [cycles] <;> omega
  · have recordsBound := record_loop_bound records s
    dsimp only [cycles]
    omega

theorem native_packet_range_execution (groups : List Nat) (records : List InteriorCodec.Record)
    (s : MachineState) (source output metadata : Nat)
    (pc : s.pc=4120) (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (count : s.getReg .x29=BitVec.ofNat 64 records.length)
    (nonempty : records≠[]) (ordered : output≤source)
    (separate : source+498*records.length+30*(capFrontierNodes groups 1 8).length≤metadata)
    (metaRoom : metadata+34≤MEMORY_BYTES)
    (footerRoom : metadata+2*(capFrontierNodes groups 1 8).length≤MEMORY_BYTES)
    (marks : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node)
    (above : 8192≤output) (metaAbove : 8192≤metadata) :
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) s coins=
      pure ⟨.success,after,cycles,0⟩) ∧
      cycles≤2273*records.length+66455+13*(capFrontierNodes groups 1 8).length := by
  have sourceRoom : source+498*records.length≤MEMORY_BYTES := by omega
  have outputRoom : output+497*records.length≤MEMORY_BYTES := by omega
  obtain ⟨recordRun,recordPC,recordSource,increment,incrementBound,recordOutput⟩ :=
    record_loop_range_execution records s source output metadata (by rw [if_neg nonempty]; exact pc)
      sourcePointer outputPointer scratch count ordered sourceRoom metaRoom
  let entry := footerInitPrefix (recordLoopState records s) 7
  have entryPC : entry.pc=12408 := by
    rw [footer_init_pc _ 7 (by decide),recordPC]
    rfl
  have positive : 0<records.length := List.length_pos_iff_ne_nil.mpr nonempty
  have entryReady : FooterRangeReady groups (capFrontierNodes groups 1 8).length entry 1
      (source+498*records.length) (output+increment) metadata 0 (s.getReg .x17) := by
    refine ⟨⟨footer_init_marks _,footer_init_limit _,?_⟩,footer_init_node _,?_,?_,?_,footer_init_count _,?_,
      by omega,by omega,footerRoom,by omega,metaAbove⟩
    · intro node bound
      rw [footer_init_memory,record_loop_range_mark_frame records s output metadata node outputPointer scratch
        outputRoom metaRoom above metaAbove bound]
      exact marks node bound
    · rw [footer_init_register _ .x5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact recordSource
    · rw [footer_init_register _ .x6 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact recordOutput
    · rw [footer_init_meta,record_loop_proof_base,scratch]
    · rw [footer_init_register _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide),record_loop_proof_base]
  obtain ⟨after,footerCycles,footerRun,footerBound⟩ :=
    footer_complete_range_execution groups entry _ _ metadata _ entryReady entryPC (by omega)
  let cycles := recordLoopCycles records s+7+footerCycles
  refine ⟨after,cycles,?_,?_⟩
  · intro fuel coins
    rw [show cycles+fuel=recordLoopCycles records s+(7+(footerCycles+fuel)) by dsimp only [cycles]; omega,
      recordRun,footer_init_execution _ recordPC,footerRun fuel coins]
    simp only [pure_bind,Execution.charge]
    congr 2 <;> dsimp only [cycles] <;> omega
  · have bound := record_loop_bound records s
    dsimp only [cycles]
    omega

end CommitGolfCandidate.Chained.Native
