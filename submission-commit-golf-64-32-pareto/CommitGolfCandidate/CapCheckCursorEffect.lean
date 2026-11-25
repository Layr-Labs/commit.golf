import CommitGolfCandidate.CapDfsCursorEffect

/-! Checker cursor and end-pointer projections for successful DFS macros.
The cursor advances only after a checked boundary copy. These are modular
register equations; natural admission and short-input rejection are separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_dfs_check_cursor_effect (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState) (cursor : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    next.getReg .x25 = BitVec.ofNat 64 (cursor + capBoundaryIncrement marked control) := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState true state node) reached
        subst next
        simp only [capBoundaryIncrement, present, ↓reduceIte, Nat.add_zero]
        rw [capMarkedVisitState, cap_known_state_register true _ node .x25 (by decide)]
        exact (cap_marked_prepare_register true state .x25 (by decide)).trans pointer
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownCheckState state) reached
        subst next
        simpa only [capBoundaryIncrement, absent, Bool.false_eq_true, ↓reduceIte] using
          cap_unknown_check_cursor state cursor pointer
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState true state) reached
        subst next
        simpa only [capBoundaryIncrement, Nat.add_zero, capAdvanceRootState] using
          (cap_flow_register _ _ .x25).trans pointer
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState true state) reached
          subst next
          simp only [capBoundaryIncrement, Nat.add_zero]
          rw [capAdvanceSiblingState, cap_flow_register,
            cap_navigation_register _ _ .x25 (by decide)]
          exact (cap_advance_guard_register true state .x25 (by decide)).trans pointer
        · simp only [capDfsStep, if_neg root, if_neg even, ↓reduceIte] at reached
          obtain ⟨answer, _, returned⟩ := mem_support_bind_peel _ _ reached
          have same := eq_of_mem_support_pure (capCheckAscentAnswer state answer) returned
          subst next
          simpa only [capBoundaryIncrement, Nat.add_zero] using
            (cap_check_ascent_answer_register state answer .x25 (by decide)).trans pointer
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      simpa only [capBoundaryIncrement, Nat.add_zero] using pointer

theorem cap_dfs_check_end_pointer (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    next.getReg .x22 = state.getReg .x22 := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState true state node) reached
        subst next
        rw [capMarkedVisitState, cap_known_state_register true _ node .x22 (by decide)]
        exact cap_marked_prepare_register true state .x22 (by decide)
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownCheckState state) reached
        subst next
        exact cap_unknown_check_register state .x22 (by decide)
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState true state) reached
        subst next
        exact cap_flow_register _ _ .x22
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState true state) reached
          subst next
          rw [capAdvanceSiblingState, cap_flow_register,
            cap_navigation_register _ _ .x22 (by decide)]
          exact cap_advance_guard_register true state .x22 (by decide)
        · simp only [capDfsStep, if_neg root, if_neg even, ↓reduceIte] at reached
          obtain ⟨answer, _, returned⟩ := mem_support_bind_peel _ _ reached
          have same := eq_of_mem_support_pure (capCheckAscentAnswer state answer) returned
          subst next
          exact cap_check_ascent_answer_register state answer .x22 (by decide)
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      rfl

end CommitGolfCandidate
