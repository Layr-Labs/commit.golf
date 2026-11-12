import CommitGolfCandidate.CapOpenFilledMarks

/-! Nonempty ABI requests produce an occupied cap root. This follows from the
same OR tree used by the actual mark pass, with no hash or memory assumption. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_tree_marks_root_false (leaves : Nat → Bool)
    (root : capTreeMarks leaves 1 = false) (node : Nat)
    (positive : 0 < node) (bounded : node < 512) :
    capTreeMarks leaves node = false := by
  induction node using Nat.strong_induction_on with
  | h node ih =>
    by_cases first : node = 1
    · simpa only [first] using root
    · have parentPositive : 0 < node/2 := by omega
      have parentBound : node/2 < 256 := by omega
      have parentLess : node/2 < node := by omega
      have parent := ih (node/2) parentLess parentPositive (by omega)
      rw [cap_tree_marks_parent leaves (node/2) parentPositive parentBound] at parent
      have both := Bool.or_eq_false_iff.mp parent
      by_cases even : node%2 = 0
      · have equality : 2*(node/2) = node := by omega
        simpa only [equality] using both.1
      · have equality : 2*(node/2)+1 = node := by omega
        simpa only [equality] using both.2

theorem cap_open_requested_marks_nonempty (positions : Positions)
    (positive : 0 < positions.card) :
    capOpenRequestedMarks positions 1 = true := by
  obtain ⟨index, member⟩ := Finset.card_pos.mp positive
  have groupBound : (capGroup index).val < 256 := (capGroup index).isLt
  have inRecords : index ∈ capOpenRequestedIndices positions := by
    simpa only [capOpenRequestedIndices, Finset.mem_sort] using member
  have seen := (cap_open_marks_seen_full (capOpenRequestedIndices positions)
    (256+(capGroup index).val)).mpr ⟨index, inRecords, rfl⟩
  have leaf : capOpenRequestedMarks positions (256+(capGroup index).val) = true := by
    rw [capOpenRequestedMarks, cap_tree_marks_leaf _ _ (by omega)]
    simpa only [capOpenRequestedIndices, Finset.length_sort] using seen
  by_contra absent
  have root : capTreeMarks
      (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card) 1 = false :=
    Bool.eq_false_iff.mpr absent
  have empty := cap_tree_marks_root_false _ root (256+(capGroup index).val)
    (by omega) (by omega)
  rw [show capTreeMarks
      (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card)
      (256+(capGroup index).val) = true from leaf] at empty
  contradiction

end CommitGolfCandidate
