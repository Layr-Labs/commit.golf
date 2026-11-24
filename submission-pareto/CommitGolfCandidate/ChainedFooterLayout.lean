import CommitGolfCandidate.ChainedFooterReady

/-! Typed raw footer fields follow the variable-width frontier in order. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

inductive FooterLayout : List Nat → List RawField → Prop
  | nil : FooterLayout [] []
  | cons {node nodes field fields} : field.low.length=29 → field.padding=[] →
      field.high.length=InteriorCodec.footerWidth node-232 → FooterLayout nodes fields →
      FooterLayout (node::nodes) (field::fields)

theorem footer_layout_count {nodes : List Nat} {fields : List RawField} (layout : FooterLayout nodes fields) :
    fields.length=nodes.length := by induction layout <;> simp_all

theorem footer_layout_raw_length {nodes : List Nat} {fields : List RawField} (layout : FooterLayout nodes fields) :
    (rawFieldsBytes fields).length=30*fields.length := by
  induction layout with
  | nil => rfl
  | cons low padding high layout ih =>
    simp only [rawFieldsBytes,List.flatMap_cons,List.length_append,RawField.bytes,low,padding,
      List.length_cons,List.length_nil] at ih ⊢
    omega

theorem footer_layout_low_length {nodes : List Nat} {fields : List RawField} (layout : FooterLayout nodes fields) :
    (rawFieldsLow fields).length=29*fields.length := by
  induction layout with
  | nil => rfl
  | cons low padding high layout ih =>
    simp only [rawFieldsLow,List.flatMap_cons,List.length_append,low,List.length_cons] at ih ⊢
    omega

theorem footer_layout_split (left right : List Nat) (fields : List RawField)
    (layout : FooterLayout (left++right) fields) :
    ∃ front back, fields=front++back ∧ FooterLayout left front ∧ FooterLayout right back := by
  induction left generalizing fields with
  | nil => exact ⟨[],fields,rfl,.nil,layout⟩
  | cons node left ih =>
    cases layout with
    | cons low padding high tail =>
      obtain ⟨front,back,equal,leftLayout,rightLayout⟩ := ih _ tail
      subst equal
      exact ⟨_::front,back,rfl,.cons low padding high leftLayout,rightLayout⟩

theorem footer_layout_empty (fields : List RawField) (layout : FooterLayout [] fields) : fields=[] := by
  cases layout
  rfl

end CommitGolfCandidate.Chained.Native
