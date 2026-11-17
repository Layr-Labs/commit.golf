import CommitGolfCandidate.CapOpenRecordsMarks
import CommitGolfCandidate.CapGroups

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def capOpenMarksSeen (records : List Index) : Nat → Nat → Bool
  | 0, _ => false
  | remaining+1, node =>
      decide (node = capOpenRecordGroup records remaining) ||
        capOpenMarksSeen records remaining node

theorem cap_open_marks_fold (records : List Index) (remaining node : Nat)
    (marks : Nat → Word) :
    capOpenMarksFinish records remaining marks node =
      if capOpenMarksSeen records remaining node then 1 else marks node := by
  induction remaining generalizing marks with
  | zero => rfl
  | succ remaining ih =>
    simp only [capOpenMarksFinish, capOpenMarksSeen, ih]
    by_cases current : node = capOpenRecordGroup records remaining
    · simp only [current, decide_true, Bool.true_or, ite_true, ite_self]
    · simp only [current, decide_false, Bool.false_or, ite_false]

theorem cap_open_marks_seen_residual (records : List Index) (remaining node : Nat) :
    capOpenMarksSeen records remaining node = true ↔
      ∃ residual < remaining, node = capOpenRecordGroup records residual := by
  induction remaining with
  | zero => simp only [capOpenMarksSeen, Bool.false_eq_true, Nat.not_lt_zero,
      false_and, exists_false]
  | succ remaining ih =>
    simp only [capOpenMarksSeen, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (same | ⟨residual, bound, same⟩)
      · exact ⟨remaining, Nat.lt_succ_self remaining, same⟩
      · exact ⟨residual, Nat.lt_succ_of_lt bound, same⟩
    · rintro ⟨residual, bound, same⟩
      by_cases last : residual = remaining
      · exact Or.inl (last ▸ same)
      · exact Or.inr ⟨residual, by omega, same⟩

theorem cap_open_marks_seen_full (records : List Index) (node : Nat) :
    capOpenMarksSeen records records.length node = true ↔
      ∃ index ∈ records, node = 256+(capGroup index).val := by
  rw [cap_open_marks_seen_residual]
  constructor
  · rintro ⟨residual, bound, same⟩
    have ordinalBound : records.length-(residual+1) < records.length := by omega
    refine ⟨records[records.length-(residual+1)]'ordinalBound,
      List.getElem_mem ordinalBound, ?_⟩
    simpa only [capOpenRecordGroup, List.getElem?_eq_getElem ordinalBound,
      Option.map_some, Option.getD_some, capGroup, Nat.reducePow] using same
  · rintro ⟨index, member, same⟩
    obtain ⟨ordinal, bound, entry⟩ := List.mem_iff_getElem.mp member
    have residualBound : records.length-(ordinal+1) < records.length := by omega
    refine ⟨records.length-(ordinal+1), residualBound, ?_⟩
    have ordinalIdentity :
        records.length-(records.length-(ordinal+1)+1) = ordinal := by omega
    simpa only [capOpenRecordGroup, ordinalIdentity, List.getElem?_eq_getElem bound,
      Option.map_some, Option.getD_some, entry, capGroup, Nat.reducePow] using same

end CommitGolfCandidate
