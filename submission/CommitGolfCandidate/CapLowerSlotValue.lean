import CommitGolfCandidate.CapLowerParser

namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false

theorem cap_lower_slot_value (record : CapLowerRecord) (part : Nat)
    (inside : part < 17) :
    (capLowerEncoding record)[part]'(by
      simp only [capLowerEncoding,List.length_cons,List.length_ofFn]; omega) =
      if zero : part = 0 then record.salt
      else record.sibling ⟨part-1,by omega⟩ := by
  cases part with
  | zero => simp only [capLowerEncoding,List.getElem_cons_zero,dite_true]
  | succ level =>
    simp only [capLowerEncoding,List.getElem_cons_succ,List.getElem_ofFn,
      Nat.succ_ne_zero,dite_false,Nat.add_sub_cancel]

end CommitGolfCandidate
