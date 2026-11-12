import CommitGolfCandidate.CapOpenBoundaryBytes

/-! Opening traversal preserves all bytes below a fixed output floor. The
floor is tracked against the actual unsigned cursor, and the natural rank window
prevents wrap. This includes the retained trapdoor heap when the floor is the
proof buffer base; it does not claim to preserve already emitted proof bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapOpenInputFrame (floor : Nat) (reference state : MachineState) : Prop :=
  ∀ address, address < floor →
    state.getByte (BitVec.ofNat 64 address) = reference.getByte (BitVec.ofNat 64 address)

private theorem byte_memory (state next : MachineState)
    (same : next.mem = state.mem) (address : Nat) :
    next.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address) := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem cap_open_step_floor (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState) (limit floor : Nat)
    (valid : CapDfsControlValid control)
    (window : CapOpenCursorWindow limit control state)
    (limitBound : limit ≤ MEMORY_BYTES)
    (before : floor ≤ (state.getReg .x25).toNat)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    floor ≤ (next.getReg .x25).toNat := by
  obtain ⟨cursor, pointer, aligned, high, space⟩ := window
  have cursorBound : cursor < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have current : (state.getReg .x25).toNat = cursor := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cursorBound]
  have incrementBound : capBoundaryIncrement marked control ≤
      32 * (1022 - capControlRank control) := by
    by_cases done : control = .done
    · subst control
      simp only [capBoundaryIncrement]
      omega
    · have rank := cap_control_rank_before_done control valid done
      have inc := cap_boundary_increment_bound marked control
      omega
  have nextBound : cursor + capBoundaryIncrement marked control < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  rw [cap_dfs_open_cursor_effect marked control state next cursor pointer reached,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt nextBound]
  rw [current] at before
  omega

theorem cap_open_step_input_frame (marked : Nat → Bool) (control : CapDfsControl)
    (state next reference : MachineState) (rootBase limit floor : Nat)
    (physical : CapDfsStateControl false state control)
    (valid : CapDfsControlValid control)
    (stable : CapDfsStable false state rootBase)
    (window : CapOpenCursorWindow limit control state)
    (limitBound : limit ≤ MEMORY_BYTES)
    (before : floor ≤ (state.getReg .x25).toNat)
    (frame : CapOpenInputFrame floor reference state)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    CapOpenInputFrame floor reference next := by
  intro address low
  suffices same : next.getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) from same.trans (frame address low)
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState false state node) reached
        subst next
        exact byte_memory state _ (cap_marked_visit_memory false state node) address
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
        subst next
        obtain ⟨cursor, pointer, aligned, high, space⟩ := window
        have rank := cap_control_rank_before_done (.visit node) valid
          (by intro impossible; cases impossible)
        have cursorBound : cursor + 32 ≤ 2^64 := by
          simp only [MEMORY_BYTES] at limitBound
          omega
        have current : (state.getReg .x25).toNat = cursor := by
          rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [current] at before
        exact cap_unknown_open_byte_before state node rootBase cursor address
          stable.roots physical.2 pointer aligned cursorBound (by omega)
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState false state) reached
        subst next
        exact byte_memory state _ (cap_flow_memory _ _) address
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState false state) reached
          subst next
          exact byte_memory state _ (cap_advance_sibling_memory false state) address
        · simp only [capDfsStep, if_neg root, if_neg even, Bool.false_eq_true,
            ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capAdvanceOpenAscentState state) reached
          subst next
          exact byte_memory state _ (cap_advance_open_ascent_memory state) address
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      rfl

end CommitGolfCandidate
