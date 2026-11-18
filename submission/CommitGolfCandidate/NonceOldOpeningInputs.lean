import CommitGolfCandidate.NonceOpeningBridge

/-! ABI inputs retained by the old opener's actual result. The count frame
is derived from its real setup, record, mark and traversal transitions. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenFinalState capOpenTraversalInitial capOpenRecordsFinal

theorem nonce_old_open_step_count (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    next.getReg .x16 = state.getReg .x16 := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState false state node) reached
        subst next
        exact cap_dfs_marked_register false state node .x16 (by decide)
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
        subst next
        exact cap_unknown_open_register state .x16 (by decide)
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState false state) reached
        subst next
        exact cap_flow_register _ _ _
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState false state) reached
          subst next
          exact cap_dfs_sibling_register false state .x16 (by decide)
        · simp only [capDfsStep, if_neg root, if_neg even, Bool.false_eq_true,
            ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capAdvanceOpenAscentState state) reached
          subst next
          exact cap_dfs_open_ascent_register state .x16 (by decide)
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      rfl

theorem nonce_old_open_run_count (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) (state final : MachineState)
    (reached : final ∈ support (capDfsRun false marked count control state)) :
    final.getReg .x16 = state.getReg .x16 := by
  induction count generalizing control state with
  | zero =>
      have same := eq_of_mem_support_pure state reached
      subst final
      rfl
  | succ count ih =>
      rw [capDfsRun] at reached
      obtain ⟨next, first, tail⟩ := mem_support_bind_peel _ _ reached
      exact (ih (capControlStep marked control) next tail).trans
        (nonce_old_open_step_count marked control state next first)

private theorem old_exit_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x10 ∧ reg ≠ .x5 ∧ reg ≠ .x11) :
    (capOpenExitState state).getReg reg=state.getReg reg := by
  simp only [capOpenExitState, capOpenLengthState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem nonce_old_traversal_count (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (capOpenTraversalInitial trapdoor positions).getReg .x16=BitVec.ofNat 64 positions.card := by
  have setup : (capOpenInitializedState
      (capProgram.initialState .opening (trapdoor,positions))).getReg .x16=
      BitVec.ofNat 64 positions.card := by
    exact (cap_open_setup_registers _).2.2.2.2.2.2.2.2.2.2
  have records : (capOpenRecordsFinal trapdoor positions).getReg .x16=
      BitVec.ofNat 64 positions.card := by
    exact (cap_open_records_final_register trapdoor positions .x16 (by decide)).trans setup
  unfold capOpenTraversalInitial
  rw [cap_open_walk_initial_register _ .x16 (by decide)]
  exact (cap_open_marked_final_register trapdoor positions .x16 (by decide)).trans records

theorem nonce_old_nonempty_count (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (capOpenNonemptyResult trapdoor positions).state.getReg .x16=BitVec.ofNat 64 positions.card := by
  change (capOpenExitState (capOpenFinalState trapdoor positions)).getReg .x16=_
  rw [old_exit_register _ .x16 (by decide)]
  exact (nonce_old_open_run_count (capOpenRequestedMarks positions) 1022 (.visit 1) _ _
    (cap_open_final_state_support trapdoor positions)).trans
      (nonce_old_traversal_count trapdoor positions)

theorem nonce_old_nonempty_base (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (capOpenNonemptyResult trapdoor positions).state.getReg .x15=
      BitVec.ofNat 64 capProgram.layout.proof := by
  change (capOpenExitState (capOpenFinalState trapdoor positions)).getReg .x15=_
  rw [old_exit_register _ .x15 (by decide)]
  exact (cap_open_run_base (capOpenRequestedMarks positions) 1022 (.visit 1) _ _
    (cap_open_final_state_support trapdoor positions)).trans
      (cap_open_traversal_initial_proof_base trapdoor positions)

theorem nonce_old_nonempty_end (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (positive : 0 < positions.card) :
    (capOpenNonemptyResult trapdoor positions).state.getReg .x25=
      BitVec.ofNat 64 (capProgram.layout.proof+576*positions.card+
        32*(capOpenBoundaryDigests trapdoor positions).length) := by
  change (capOpenExitState (capOpenFinalState trapdoor positions)).getReg .x25=_
  rw [old_exit_register _ .x25 (by decide)]
  have pointer:=cap_open_run_cursor_count (capOpenRequestedMarks positions) 1022 (.visit 1)
    _ _ (capProgram.layout.proof+576*positions.card)
    (cap_open_traversal_initial_cursor trapdoor positions positive)
    (cap_open_final_state_support trapdoor positions)
  simpa only [capOpenBoundaryDigests, List.length_map, Nat.add_assoc] using pointer

end CommitGolfCandidate
