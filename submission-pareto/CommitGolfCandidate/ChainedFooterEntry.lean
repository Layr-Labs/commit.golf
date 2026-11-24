import CommitGolfCandidate.ChainedRecordMarks

/-! Connect the finished native record stream to the complete typed footer ABI. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
open TwoPermutationPrototype.Opening
set_option maxRecDepth 8192

theorem footer_initial_ready (groups : List Nat) (fields : List RawField) (suffix past : Proof)
    (s : MachineState) (source outputBase metadata : Nat)
    (ready : RecordStreamReady [] (rawFieldsBytes fields++suffix) s source (outputBase+past.length) metadata)
    (memory : BytesAt s (BitVec.ofNat 64 outputBase) past)
    (base : s.getReg .x17=BitVec.ofNat 64 outputBase)
    (marks : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node)
    (above : 8192≤outputBase) (metaAbove : 8192≤metadata)
    (capacity : metadata+2*fields.length≤MEMORY_BYTES) :
    FooterReady groups fields suffix past [] (footerInitPrefix s 7) 1 source outputBase metadata := by
  have entry := record_stream_footer_entry (rawFieldsBytes fields++suffix) s source (outputBase+past.length) metadata ready
  refine ⟨⟨footer_init_marks s,footer_init_limit s,?_⟩,?_,footer_init_node s,footer_init_count s,rfl,
    above,metaAbove,?_,?_⟩
  · intro node bound
    rw [footer_init_memory]
    exact marks node bound
  · refine ⟨entry.2.1,entry.2.2.1,?_,entry.2.2.2.2,?_,?_,ready.ordered,?_,?_⟩
    · simpa only [List.length_nil,Nat.add_zero] using entry.2.2.2.1
    · intro index inside
      rw [footer_init_byte]
      exact memory index inside
    · intro index inside
      simp at inside
    · have separate := ready.separate
      simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.length_append,Nat.add_assoc] using separate
    · simp only [List.length_nil,Nat.add_zero]
      unfold MEMORY_BYTES at capacity
      omega
  · simpa only [List.length_nil,Nat.add_zero] using capacity
  · rw [footer_init_register _ .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact base

theorem record_loop_footer_ready (groups : List Nat) (records : List InteriorCodec.Record) (fields : List RawField)
    (suffix : Proof) (s : MachineState) (source outputBase metadata : Nat)
    (ready : RecordStreamReady records (rawFieldsBytes fields++suffix) s source outputBase metadata)
    (base : s.getReg .x17=BitVec.ofNat 64 outputBase)
    (marks : ∀ node, node<512 → s.getMem (BitVec.ofNat 64 (4096+8*node))=markWord groups node)
    (above : 8192≤outputBase) (metaAbove : 8192≤metadata)
    (capacity : metadata+2*fields.length≤MEMORY_BYTES) :
    FooterReady groups fields suffix (encodedRecords records) [] (footerInitPrefix (recordLoopState records s) 7)
      1 (source+498*records.length) outputBase metadata := by
  have completed := record_loop_ready records (rawFieldsBytes fields++suffix) s source outputBase metadata ready
  rw [←encoded_records_length] at completed
  apply footer_initial_ready groups fields suffix (encodedRecords records) _ _ outputBase metadata completed
    (record_loop_memory records (rawFieldsBytes fields++suffix) s source outputBase metadata ready)
    ((record_loop_proof_base records s).trans base) _ above metaAbove capacity
  intro node bound
  rw [record_loop_mark_frame records (rawFieldsBytes fields++suffix) s source outputBase metadata node ready above bound]
  exact marks node bound

end CommitGolfCandidate.Chained.Native
