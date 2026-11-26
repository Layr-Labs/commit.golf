import CommitGolfCandidate.ChainedTailParseExecution

/-! Reconstruct typed split-width fields from the native inverse's scratch rows. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf SplitCodec

def fieldsFromRows : (spec : Spec) → List Bool → List (List Bool) → Payload spec
  | [],_,_ => .nil
  | (low,high)::spec,front,rows =>
    .cons (word low high front (rows.headD [])) (fieldsFromRows spec (front.drop low) rows.tail)

theorem word_tail_prefix (low high : Nat) (front row rest : List Bool) (width : row.length=high) :
    word low high front (row++rest)=word low high front row := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [word,BitVec.getLsbD_ofFnLE,dite_eq_left inside]
  by_cases before : bit<low
  · rw [ite_eq_left before,ite_eq_left before]
  · rw [ite_eq_right before,ite_eq_right before]
    exact List.getD_append row rest false (bit-low) (by rw [width]; omega)

theorem fields_from_rows (spec : Spec) (front : List Bool) (rows : List (List Bool)) (carry : List Bool)
    (widths : rows.map List.length=spec.map Prod.snd) :
    fieldsFromRows spec front rows=fields spec front (rows.flatten++carry) := by
  induction spec generalizing front rows with
  | nil => rfl
  | cons field spec ih =>
    obtain ⟨low,high⟩ := field
    cases rows with
    | nil => simp at widths
    | cons row rows =>
      have parts : row.length=high ∧ rows.map List.length=spec.map Prod.snd := by simpa using widths
      simp only [fieldsFromRows,List.headD_cons,List.tail_cons,List.flatten_cons,fields,List.append_assoc]
      rw [word_tail_prefix low high front row (rows.flatten++carry) parts.1,
        List.drop_left' parts.1,←ih (front.drop low) rows parts.2]

theorem inverse_plan_fields (spec : Spec) (front : List Bool) (input : Nat → List Bool)
    (byteSize : ∀ i, (input i).length=8) (small : ∀ field ∈ spec, field.2≤6) :
    let plan := tailParsePlan (spec.map Prod.snd) [] input
    fieldsFromRows spec front plan.fields=fields spec front (pullBitBytes input plan.read) := by
  have widths : ∀ width ∈ spec.map Prod.snd, width≤6 := by
    intro width member
    obtain ⟨field,belongs,rfl⟩ := List.mem_map.mp member
    exact small field belongs
  have shape := tail_parse_plan_widths (spec.map Prod.snd) [] input byteSize widths
  have result := fields_from_rows spec front (tailParsePlan (spec.map Prod.snd) [] input).fields
    (tailParsePlan (spec.map Prod.snd) [] input).carry shape
  rw [tail_parse_plan_bits,List.nil_append] at result
  exact result

end CommitGolfCandidate.Chained.Native
