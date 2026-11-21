import CommitGolfCandidate.ChainedInverseFooterEntry
import CommitGolfCandidate.ChainedFooterPayload

/-! Typed footer payloads instantiate the native inverse loop's field layout. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 SplitCodec

theorem footer_layout_inverse_shapes {nodes : List Nat} {fields : List RawField}
    (layout : FooterLayout nodes fields) :
    (∀ field ∈ fields, field.low.length=29) ∧ (∀ field ∈ fields, field.padding=[]) := by
  induction layout with
  | nil => simp
  | cons low padding high tail ih =>
    constructor
    · intro field member
      rcases List.mem_cons.mp member with rfl | member
      · exact low
      · exact ih.1 field member
    · intro field member
      rcases List.mem_cons.mp member with rfl | member
      · exact padding
      · exact ih.2 field member

theorem native_inverse_footer_payload (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes))
    (suffix completed : Proof) (s : MachineState) (source outputBase metadata : Nat)
    (ready : InverseFieldsReady (footerRawFields nodes footer) suffix completed s source outputBase metadata)
    (skip : s.getReg .x9=1#64) :
    InverseFieldsReady [] suffix (completed++rawFieldsBytes (footerRawFields nodes footer))
      (inverseFooterRowsState nodes.length (inverseFooterEntryState s)) (source+29*nodes.length)
      outputBase (metadata+2*nodes.length) := by
  have layout := footer_raw_fields_layout nodes footer
  have shape := footer_layout_inverse_shapes layout
  have result := inverse_footer_memory (footerRawFields nodes footer) suffix completed s source outputBase metadata
    ready shape.1 shape.2 skip
  simpa only [footer_layout_low_length layout,footer_raw_fields_count] using result

end CommitGolfCandidate.Chained.Native
