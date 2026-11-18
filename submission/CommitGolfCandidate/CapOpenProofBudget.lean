import CommitGolfCandidate.CapOpenCursorCount
import CommitGolfCandidate.CapHeapView
import CommitGolfCandidate.CapOpenExit

/-! Honest cap-size accounting reaches the actual reported byte displacement.
The caller supplies the populated lower-record prefix and finalized mark
equations; the complete opening theorem is stated separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_boundary_length (compress : Compression) (roots : Nat → Digest)
    (marked : Nat → Bool)
    (hashParents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (markParents : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (nonempty : marked 1 = true) :
    (capControlBoundaries marked 1022 (.visit 1)).length ≤ 128 := by
  have selected := congrArg List.length
    (cap_heap_serialization compress roots marked hashParents markParents)
  simp only [List.length_map] at selected
  rw [selected]
  apply cap_occupied_proof_bound
  exact (cap_heap_view_occupied roots marked markParents 8 1
    (by decide) (by decide)).trans nonempty

theorem cap_open_step_base (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    next.getReg .x15 = state.getReg .x15 := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState false state node) reached
        subst next
        exact cap_dfs_marked_register false state node .x15 (by decide)
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
        subst next
        exact cap_unknown_open_register state .x15 (by decide)
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
          exact cap_dfs_sibling_register false state .x15 (by decide)
        · simp only [capDfsStep, if_neg root, if_neg even, Bool.false_eq_true,
            ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capAdvanceOpenAscentState state) reached
          subst next
          exact cap_dfs_open_ascent_register state .x15 (by decide)
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      rfl

theorem cap_open_run_base (marked : Nat → Bool) (count : Nat)
    (control : CapDfsControl) (state final : MachineState)
    (reached : final ∈ support (capDfsRun false marked count control state)) :
    final.getReg .x15 = state.getReg .x15 := by
  induction count generalizing control state with
  | zero =>
      have same := eq_of_mem_support_pure state reached
      subst final
      rfl
  | succ count ih =>
      rw [capDfsRun] at reached
      obtain ⟨next, first, tail⟩ := mem_support_bind_peel _ _ reached
      exact (ih (capControlStep marked control) next tail).trans
        (cap_open_step_base marked control state next first)

theorem cap_open_batch_report_bound (compress : Compression) (roots : Nat → Digest)
    (marked : Nat → Bool)
    (hashParents : ∀ node, 0 < node → node < 256 →
      roots node = combine compress (roots (2*node)) (roots (2*node+1)))
    (markParents : ∀ node, 0 < node → node < 256 →
      marked node = (marked (2*node) || marked (2*node+1)))
    (nonempty : marked 1 = true)
    (state final : MachineState)
    (base : state.getReg .x15 = BitVec.ofNat 64 capProgram.layout.proof)
    (prefixCursor : state.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + 576*128))
    (reached : final ∈ support (capDfsRun false marked 1022 (.visit 1) state)) :
    ((capOpenExitState final).getReg .x11).toNat ≤ 77824 := by
  let boundaries := (capControlBoundaries marked 1022 (.visit 1)).length
  have bounded : boundaries ≤ 128 :=
    cap_open_boundary_length compress roots marked hashParents markParents nonempty
  have start := (cap_open_run_base marked 1022 (.visit 1) state final reached).trans base
  have finish := cap_open_run_cursor_count marked 1022 (.visit 1) state final
    (capProgram.layout.proof + 576*128) prefixCursor reached
  have cursor : final.getReg .x25 =
      BitVec.ofNat 64 (capProgram.layout.proof + (576*128 + 32*boundaries)) := by
    simpa only [Nat.add_assoc] using finish
  have noWrap : capProgram.layout.proof + (576*128 + 32*boundaries) < 2^64 := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    omega
  rw [cap_open_exit_report final capProgram.layout.proof _ start cursor noWrap]
  omega

end CommitGolfCandidate
