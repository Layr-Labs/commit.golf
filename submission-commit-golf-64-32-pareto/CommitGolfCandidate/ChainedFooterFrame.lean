import CommitGolfCandidate.ChainedFooterTailSetup

/-! Footer fields preserve old output, old descriptors and the aligned mark array. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

theorem low_copy_byte_frame (n : Nat) (s : MachineState) (query : Word)
    (apart : ∀ index, index<n → query≠s.getReg .x6+BitVec.ofNat 64 index) :
    (lowCopyState n s).getByte query=s.getByte query := by
  induction n generalizing s with
  | zero => rw [low_copy_zero]
  | succ n ih =>
    have next : ∀ index, index<n → query≠(byteCopyPrefix s 4).getReg .x6+BitVec.ofNat 64 index := by
      intro index inside
      rw [byte_copy_destination,byte_offset_succ]
      exact apart (index+1) (by omega)
    rw [low_copy_succ,ih _ next,byte_copy_byte]
    exact ite_eq_right (by simpa only [BitVec.add_zero] using apart 0 (by omega))

theorem footer_emit_byte_frame (s : MachineState) (query : Word)
    (output : ∀ index, index<29 → query≠s.getReg .x6+BitVec.ofNat 64 index)
    (metadata : query≠s.getReg .x7 ∧ query≠s.getReg .x7+1) :
    (footerEmitState s).getByte query=s.getByte query := by
  rw [footerEmitState,footer_count_byte,fieldBuildState,field_descriptor_byte,
    low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),
    footer_header_register _ .x7 (by decide) (by decide),
    ite_eq_right metadata.2,ite_eq_right metadata.1,low_copy_byte_frame]
  · exact footer_header_byte s query
  · intro index inside
    rw [footer_header_register _ .x6 (by decide) (by decide)]
    exact output index inside

theorem footer_emit_preserves_bytes (bytes : Proof) (s : MachineState) (output metadata base : Nat)
    (outputReg : s.getReg .x6=BitVec.ofNat 64 output) (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (memory : BytesAt s (BitVec.ofNat 64 base) bytes)
    (outputFit : output+29<2^64) (metaFit : metadata+2<2^64) (baseFit : base+bytes.length<2^64)
    (apartOutput : base+bytes.length≤output ∨ output+29≤base)
    (apartMeta : base+bytes.length≤metadata ∨ metadata+2≤base) :
    BytesAt (footerEmitState s) (BitVec.ofNat 64 base) bytes := by
  intro index inside
  rw [footer_emit_byte_frame]
  · exact memory index inside
  · intro written before
    rw [outputReg,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by omega)
    rcases apartOutput with left | right <;> omega
  · rw [metaReg,←BitVec.ofNat_add]
    constructor
    · apply word_of_nat_ne _ _ (by omega) (by omega)
      rcases apartMeta with left | right <;> omega
    · change BitVec.ofNat 64 (base+index)≠BitVec.ofNat 64 metadata+BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      apply word_of_nat_ne _ _ (by omega) (by omega)
      rcases apartMeta with left | right <;> omega

theorem native_read_aligned_word (s : MachineState) (address : Nat) (aligned : address%8=0) :
    readBuffer s address 8=s.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice s address 32 0 8 (by decide)
  have assembled := read_digest_word s address 0 aligned (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,BitVec.setWidth_eq] using slice.symm.trans assembled

theorem aligned_word_of_byte_frame (before after : MachineState) (address : Nat) (aligned : address%8=0)
    (frame : ∀ index, index<8 → after.getByte (BitVec.ofNat 64 (address+index))=
      before.getByte (BitVec.ofNat 64 (address+index))) :
    after.getMem (BitVec.ofNat 64 address)=before.getMem (BitVec.ofNat 64 address) := by
  rw [←native_read_aligned_word after address aligned,←native_read_aligned_word before address aligned]
  unfold readBuffer
  apply congrArg (BitVec.ofNat 64)
  apply Finset.sum_congr rfl
  intro index inside
  rw [frame index (Finset.mem_range.mp inside)]

theorem footer_emit_word_frame (s : MachineState) (output metadata address : Nat)
    (outputReg : s.getReg .x6=BitVec.ofNat 64 output) (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (outputFit : output+29<2^64) (metaFit : metadata+2<2^64) (addressFit : address+8<2^64)
    (aligned : address%8=0) (apartOutput : address+8≤output ∨ output+29≤address)
    (apartMeta : address+8≤metadata ∨ metadata+2≤address) :
    (footerEmitState s).getMem (BitVec.ofNat 64 address)=s.getMem (BitVec.ofNat 64 address) := by
  apply aligned_word_of_byte_frame s _ address aligned
  intro index inside
  apply footer_emit_byte_frame
  · intro written before
    rw [outputReg,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by omega)
    rcases apartOutput with left | right <;> omega
  · rw [metaReg]
    constructor
    · apply word_of_nat_ne _ _ (by omega) (by omega)
      rcases apartMeta with left | right <;> omega
    · change BitVec.ofNat 64 (address+index)≠BitVec.ofNat 64 metadata+BitVec.ofNat 64 1
      rw [←BitVec.ofNat_add]
      apply word_of_nat_ne _ _ (by omega) (by omega)
      rcases apartMeta with left | right <;> omega

theorem footer_emit_mark_frame (s : MachineState) (output metadata node : Nat)
    (outputReg : s.getReg .x6=BitVec.ofNat 64 output) (metaReg : s.getReg .x7=BitVec.ofNat 64 metadata)
    (outputFit : output+29<2^64) (metaFit : metadata+2<2^64)
    (outputAbove : 8192≤output) (metaAbove : 8192≤metadata) (nodeBound : node<512) :
    (footerEmitState s).getMem (BitVec.ofNat 64 (4096+8*node))=
      s.getMem (BitVec.ofNat 64 (4096+8*node)) := by
  apply footer_emit_word_frame s output metadata _ outputReg metaReg outputFit metaFit
  · omega
  · omega
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)

end CommitGolfCandidate.Chained.Native
