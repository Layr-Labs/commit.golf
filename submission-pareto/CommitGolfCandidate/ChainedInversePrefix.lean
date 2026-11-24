import CommitGolfCandidate.ChainedDecodeParts

/-! Unread bytes do not affect the inverse's fields, residual bits or cursor. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

theorem parsed_rows_unique (left right : List (List Bool)) (leftCarry rightCarry : List Bool)
    (shape : left.map List.length=right.map List.length)
    (bits : left.flatten++leftCarry=right.flatten++rightCarry) :
    left=right ∧ leftCarry=rightCarry := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons row rows ih =>
    cases right with
    | nil => simp at shape
    | cons other rest =>
      have parts : row.length=other.length ∧ rows.map List.length=rest.map List.length := by simpa using shape
      have grouped : row++(rows.flatten++leftCarry)=other++(rest.flatten++rightCarry) := by
        simpa only [List.flatten_cons,List.append_assoc] using bits
      have taken := congrArg (List.take row.length) grouped
      have own : (row++(rows.flatten++leftCarry)).take row.length=row := by simp
      have otherTake : (other++(rest.flatten++rightCarry)).take row.length=other := by rw [parts.1]; simp
      have same := own.symm.trans (taken.trans otherTake)
      rw [same] at grouped
      obtain ⟨restSame,carrySame⟩ := ih rest parts.2 (List.append_cancel_left grouped)
      exact ⟨by rw [same,restSame],carrySame⟩

theorem pull_bit_bytes_congr (left right : Nat → List Bool) (count : Nat)
    (same : ∀ index, index<count → left index=right index) :
    pullBitBytes left count=pullBitBytes right count := by
  induction count generalizing left right with
  | zero => rfl
  | succ count ih =>
    rw [pullBitBytes,pullBitBytes,same 0 (by omega),ih]
    intro index inside
    exact same (1+index) (by omega)

theorem inverse_plan_prefix (widths : List Nat) (left right : Nat → List Bool)
    (leftSize : ∀ i, (left i).length=8) (rightSize : ∀ i, (right i).length=8)
    (small : ∀ width ∈ widths, width≤6)
    (same : ∀ index, index<(widths.sum+7)/8 → left index=right index) :
    (tailParsePlan widths [] left).fields=(tailParsePlan widths [] right).fields ∧
    (tailParsePlan widths [] left).carry=(tailParsePlan widths [] right).carry ∧
    (tailParsePlan widths [] left).read=(tailParsePlan widths [] right).read := by
  have leftRead := inverse_plan_read_exact widths left leftSize small
  have rightRead := inverse_plan_read_exact widths right rightSize small
  have shape := (tail_parse_plan_widths widths [] left leftSize small).trans
    (tail_parse_plan_widths widths [] right rightSize small).symm
  have bits : (tailParsePlan widths [] left).fields.flatten++(tailParsePlan widths [] left).carry=
      (tailParsePlan widths [] right).fields.flatten++(tailParsePlan widths [] right).carry := by
    rw [tail_parse_plan_bits,tail_parse_plan_bits,List.nil_append,List.nil_append,leftRead,rightRead]
    exact pull_bit_bytes_congr left right _ same
  have rows := parsed_rows_unique _ _ _ _ shape bits
  exact ⟨rows.1,rows.2,leftRead.trans rightRead.symm⟩

end CommitGolfCandidate.Chained.Native
