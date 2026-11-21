import CommitGolfCandidate.ChainedOpeningEmpty

/-! Compose the actual nonempty entry with complete record/footer packing and halt. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp SplitCodec
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem native_opening_nonempty (groups : List Nat) (records : List InteriorCodec.Record)
    (footer : Payload (InteriorCodec.footerSpec (capFrontierNodes groups 1 8))) (suffix : Proof)
    (s : MachineState) (output : Nat) (pc : s.pc=4096) (nonempty : records≠[])
    (count : s.getReg .x16=BitVec.ofNat 64 records.length) (pointer : s.getReg .x20=BitVec.ofNat 64 output)
    (memory : BytesAt s (BitVec.ofNat 64 output)
      (rawRecordStream records++rawFieldsBytes (footerRawFields (capFrontierNodes groups 1 8) footer)++suffix))
    (marks : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node)
    (above : 8192≤output)
    (separate : output+(rawRecordStream records++rawFieldsBytes
      (footerRawFields (capFrontierNodes groups 1 8) footer)++suffix).length≤output+2^33)
    (capacity : output+2^33+max 34 (2*(capFrontierNodes groups 1 8).length)≤MEMORY_BYTES) :
    ∃ after cycles, (∀ fuel coins, execute openingControllerImage (cycles+fuel) s coins=pure ⟨.success,after,cycles,0⟩) ∧
      BytesAt after (BitVec.ofNat 64 output) (encodedRecords records++encode footer) ∧
      after.getReg .x6=BitVec.ofNat 64 (output+(encodedRecords records).length+(encode footer).length) ∧
      (after.getReg .x11).toNat=(encodedRecords records).length+(encode footer).length ∧
      cycles≤2273*records.length+66460+13*(capFrontierNodes groups 1 8).length := by
  have c34 : output+2^33+34≤MEMORY_BYTES := by
    have := Nat.le_max_left 34 (2*(capFrontierNodes groups 1 8).length)
    omega
  have cFooter : output+2^33+2*(capFrontierNodes groups 1 8).length≤MEMORY_BYTES := by
    have := Nat.le_max_right 34 (2*(capFrontierNodes groups 1 8).length)
    omega
  have ready := opening_entry_ready records
    (rawFieldsBytes (footerRawFields (capFrontierNodes groups 1 8) footer)++suffix) s output pc nonempty count pointer
    (by simpa only [List.append_assoc] using memory)
    (by simpa only [List.length_append,raw_record_stream_length,Nat.add_assoc] using separate) c34
  have kept : ∀ node, node<512 → (openingEntryPrefix s 5).getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node := by
    intro node small
    rw [opening_entry_memory]
    exact marks node small
  obtain ⟨after,cycles,ran,bytes,cursor,length,bound⟩ := native_packet_pack groups records footer suffix
    (openingEntryPrefix s 5) output output (output+2^33) ready nonempty
    ((opening_entry_data s).2.2.1.trans pointer) kept above (by omega) cFooter
  refine ⟨after,cycles+5,?_,bytes,cursor,length,by omega⟩
  intro fuel coins
  rw [show cycles+5+fuel=5+(cycles+fuel) by omega,opening_entry_execution s pc,ran]
  simp only [pure_bind,Execution.charge,Nat.add_comm]

end CommitGolfCandidate.Chained.Native
