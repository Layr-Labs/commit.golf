import CommitGolfCandidate.ChainedFooterSubtree
import CommitGolfCandidate.ChainedPayloadFields

/-! The actual footer raw-field layout is supplied by its typed codec payload. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

theorem footer_raw_fields_layout (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    FooterLayout nodes (footerRawFields nodes footer) := by
  induction nodes with
  | nil => cases footer; exact .nil
  | cons node nodes ih =>
    cases footer with
    | cons value rest =>
      apply FooterLayout.cons
      · simp only [packed_bits_length,List.length_ofFn]
      · rfl
      · simp only [List.length_ofFn]
      · exact ih rest

theorem footer_raw_fields_low (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    rawFieldsLow (footerRawFields nodes footer)=lowBytes footer :=
  payload_raw_fields_low footer [] _ _

theorem footer_raw_fields_meta (nodes : List Nat) (footer : Payload (InteriorCodec.footerSpec nodes)) :
    rawFieldsMeta (footerRawFields nodes footer)=descriptorBytes (highRows footer) := by
  rw [raw_fields_meta_rows,footerRawFields,payload_raw_fields_high]

end CommitGolfCandidate.Chained.Native
