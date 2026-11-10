import CommitGolfCandidate.CapTreeMarks

/-! Occupancy is exactly the existence of a marked descendant leaf. The
interval form avoids a logarithm or a choice of digest values. This pure
structural fact supports selecting an old opening sibling without oracle
queries; no byte-selector or hiding claim is made here. -/
namespace CommitGolfCandidate
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem cap_mark_descendant (leaves : Nat → Bool) (height node : Nat)
    (lower : 128 ≤ node*2^height) (upper : (node+1)*2^height ≤ 256) :
    capTreeMarks leaves node=true ↔
      ∃ leaf, node*2^height ≤ leaf ∧ leaf < (node+1)*2^height ∧
        leaves leaf=true := by
  induction height generalizing node with
  | zero =>
    simp only [Nat.pow_zero,Nat.mul_one] at lower upper ⊢
    rw [cap_tree_marks_leaf leaves node lower]
    constructor
    · intro marked
      exact ⟨node,le_rfl,by omega,marked⟩
    · rintro ⟨leaf,left,right,marked⟩
      have same : leaf=node := by omega
      simpa only [same] using marked
  | succ height ih =>
    have power : 0 < 2^height := Nat.two_pow_pos height
    have lower' := lower
    have upper' := upper
    rw [pow_succ] at lower' upper'
    have positive : 0 < node := by nlinarith
    have internal : node < 128 := by nlinarith
    have leftLower : 128 ≤ (2*node)*2^height := by nlinarith
    have leftUpper : (2*node+1)*2^height ≤ 256 := by nlinarith
    have rightLower : 128 ≤ (2*node+1)*2^height := by nlinarith
    have rightUpper : (2*node+1+1)*2^height ≤ 256 := by nlinarith
    rw [cap_tree_marks_parent leaves node positive internal,
      Bool.or_eq_true,ih (2*node) leftLower leftUpper,
      ih (2*node+1) rightLower rightUpper]
    constructor
    · rintro (⟨leaf,left,right,marked⟩ | ⟨leaf,left,right,marked⟩)
      · refine ⟨leaf,?_,?_,marked⟩ <;> rw [pow_succ] <;> nlinarith
      · refine ⟨leaf,?_,?_,marked⟩ <;> rw [pow_succ] <;> nlinarith
    · rintro ⟨leaf,left,right,marked⟩
      rw [pow_succ] at left right
      by_cases first : leaf < (2*node+1)*2^height
      · exact Or.inl ⟨leaf,by nlinarith,first,marked⟩
      · exact Or.inr ⟨leaf,by omega,by nlinarith,marked⟩

end CommitGolfCandidate
