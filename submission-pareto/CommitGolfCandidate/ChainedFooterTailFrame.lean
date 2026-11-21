import CommitGolfCandidate.ChainedOpeningFinish

/-! Complete footer-tail cursor arithmetic and preservation of earlier records. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec
set_option maxRecDepth 8192

theorem footer_tail_entry_buffer (s : MachineState) (buffer : TailBuffer s []) : TailBuffer (tailEntryState s) [] := by
  constructor
  · simpa only [tail_entry_register] using buffer.value
  · simpa only [tail_entry_register] using buffer.count
  · simpa only [tail_entry_register] using buffer.eight
  · exact buffer.pending

theorem footer_tail_entry_rows (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) (ready : FooterTailReady nodes footer s output metadata) :
    BytesAt (tailEntryState s) ((tailEntryState s).getReg .x21) (descriptorBytes (highRows footer)) := by
  intro index inside
  rw [tail_entry_register,ready.source]
  simp only [MachineState.getByte,tail_entry_memory]
  exact ready.rows index inside

theorem footer_tail_entry_apart (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) (ready : FooterTailReady nodes footer s output metadata) :
    TailApart ((tailEntryState s).getReg .x21) ((tailEntryState s).getReg .x20) (highRows footer) := by
  simpa only [tail_entry_register] using ready.apart

theorem footer_tail_cursor (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (output metadata : Nat) (ready : FooterTailReady nodes footer s output metadata) :
    (tailTraverseState nodes.length s).getReg .x20=BitVec.ofNat 64 (output+(encode footer).length) := by
  have cursor := native_tail_cursor (highRows footer) [] (tailEntryState s)
    (footer_tail_entry_buffer s ready.buffer) (footer_rows_small nodes footer)
    (footer_tail_entry_rows nodes footer s output metadata ready) (footer_tail_entry_apart nodes footer s output metadata ready)
  have count : (highRows footer).length=nodes.length := (high_rows_length footer).trans (List.length_map _)
  have encoding : (encode footer).length=(lowBytes footer).length+(packedBits (highRows footer).flatten).length := by
    rw [footer_descriptor_encoding,List.length_append]
  change (tailFinishState (tailFieldsState nodes.length (tailEntryState s))).getReg .x20=_
  rw [count,List.nil_append,tail_entry_register,ready.cursor,←BitVec.ofNat_add] at cursor
  rw [encoding]
  simpa only [Nat.add_assoc] using cursor

theorem footer_tail_prefix (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (s : MachineState) (base metadata : Nat) (past : Proof)
    (ready : FooterTailReady nodes footer s (base+past.length) metadata)
    (memory : BytesAt s (BitVec.ofNat 64 base) past)
    (fit : base+past.length+(encode footer).length<2^64) :
    BytesAt (tailTraverseState nodes.length s) (BitVec.ofNat 64 base) past := by
  have length : (InteriorCodec.footerSpec nodes).length=nodes.length := List.length_map _
  have encoding : (encode footer).length=(lowBytes footer).length+(packedBits (highs footer)).length := by
    rw [footer_descriptor_encoding,List.length_append,high_rows_flatten]
  rw [encoding] at fit
  intro index inside
  change (tailFinishState (tailFieldsState nodes.length (tailEntryState s))).getByte _=_
  rw [←length,native_descriptor_memory footer _ (footer_tail_entry_buffer s ready.buffer) (footer_fields_small nodes)
    (footer_tail_entry_rows nodes footer s _ _ ready) (footer_tail_entry_apart nodes footer s _ _ ready)]
  rw [write_byte_list_preserves]
  · simp only [MachineState.getByte,tail_entry_memory]
    exact memory index inside
  · intro written bounded
    rw [tail_entry_register,ready.cursor,←BitVec.ofNat_add,←BitVec.ofNat_add]
    apply word_of_nat_ne _ _ (by omega) (by omega) (by omega)

end CommitGolfCandidate.Chained.Native
