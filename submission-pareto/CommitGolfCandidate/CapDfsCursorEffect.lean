import CommitGolfCandidate.CapDfsMachineRun

/-! The opening cursor changes only when a boundary digest is emitted.
This projection is independent of memory contents and does not assert access
validity. The rank-window invariant supplies that separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capBoundaryIncrement (marked : Nat → Bool) : CapDfsControl → Nat
  | .visit node => if marked node then 0 else 32
  | _ => 0

theorem cap_dfs_open_cursor_effect (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState) (cursor : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    next.getReg .x25 = BitVec.ofNat 64 (cursor + capBoundaryIncrement marked control) := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState false state node) reached
        subst next
        simp only [capBoundaryIncrement, present, ↓reduceIte, Nat.add_zero]
        rw [capMarkedVisitState, cap_known_state_register false _ node .x25 (by decide)]
        exact (cap_marked_prepare_register false state .x25 (by decide)).trans pointer
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
        subst next
        simpa only [capBoundaryIncrement, absent, Bool.false_eq_true, ↓reduceIte] using
          cap_unknown_open_cursor state cursor pointer
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState false state) reached
        subst next
        simpa only [capBoundaryIncrement, Nat.add_zero, capAdvanceRootState] using
          (cap_flow_register _ _ .x25).trans pointer
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState false state) reached
          subst next
          simp only [capBoundaryIncrement, Nat.add_zero]
          rw [capAdvanceSiblingState, cap_flow_register,
            cap_navigation_register _ _ .x25 (by decide)]
          exact (cap_advance_guard_register false state .x25 (by decide)).trans pointer
        · simp only [capDfsStep, if_neg root, if_neg even, Bool.false_eq_true,
            ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capAdvanceOpenAscentState state) reached
          subst next
          simp only [capBoundaryIncrement, Nat.add_zero]
          rw [capAdvanceOpenAscentState, cap_flow_register,
            cap_navigation_register _ _ .x25 (by decide)]
          exact (cap_advance_guard_register false state .x25 (by decide)).trans pointer
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      simpa only [capBoundaryIncrement, Nat.add_zero] using pointer

theorem cap_boundary_increment_bound (marked : Nat → Bool) (control : CapDfsControl) :
    capBoundaryIncrement marked control ≤ 32 := by
  cases control <;> simp only [capBoundaryIncrement]
  · split <;> omega
  · omega
  · omega

theorem cap_boundary_increment_aligned (marked : Nat → Bool) (control : CapDfsControl) :
    capBoundaryIncrement marked control % 8 = 0 := by
  cases control <;> simp only [capBoundaryIncrement]
  split <;> decide

end CommitGolfCandidate
