import CommitGolfCandidate.CapDfsBoundaryOrder

/-! Every emitted unknown node is a real node of the fixed eight-level cap.
The bound depends only on control validity, not root values or replies. -/
namespace CommitGolfCandidate

theorem cap_control_boundaries_length (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) :
    (capControlBoundaries marked count control).length ≤ count := by
  induction count generalizing control with
  | zero => simp [capControlBoundaries]
  | succ count ih =>
      have head : (capControlBoundaryHead marked control).length ≤ 1 := by
        cases control with
        | visit node => simp only [capControlBoundaryHead]; split <;> simp
        | advance node => simp [capControlBoundaryHead]
        | done => simp [capControlBoundaryHead]
      rw [capControlBoundaries, List.length_append]
      have tail := ih (capControlStep marked control)
      omega

theorem cap_control_boundaries_nodes (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) (valid : CapDfsControlValid control)
    (node : Nat) (member : node ∈ capControlBoundaries marked count control) :
    0 < node ∧ node < 512 := by
  induction count generalizing control with
  | zero => simp [capControlBoundaries] at member
  | succ count ih =>
      rw [capControlBoundaries, List.mem_append] at member
      rcases member with head | tail
      · cases control with
        | advance index => simp [capControlBoundaryHead] at head
        | done => simp [capControlBoundaryHead] at head
        | visit index =>
          by_cases present : marked index = true
          · simp [capControlBoundaryHead, present] at head
          · have absent : marked index = false := Bool.eq_false_iff.mpr present
            have same : node = index := by
              simpa [capControlBoundaryHead, absent] using head
            subst node
            exact valid
      · exact ih _ (cap_control_step_valid marked control valid) tail

end CommitGolfCandidate
