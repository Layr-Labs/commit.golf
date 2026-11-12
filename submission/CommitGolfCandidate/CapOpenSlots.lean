import CommitGolfCandidate.CapOpenCursorCount

/-! Slot-level refinement of actual cap output. Every supported traversal
emits the canonical boundary roots in order. The initial root-byte frame and
admitted cursor window remain explicit; lower-record emission is separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_step_cursor_nat (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState) (limit : Nat)
    (valid : CapDfsControlValid control)
    (window : CapOpenCursorWindow limit control state)
    (limitBound : limit ≤ MEMORY_BYTES)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    (next.getReg .x25).toNat = (state.getReg .x25).toNat +
      32 * (capControlBoundaryHead marked control).length := by
  obtain ⟨cursor, pointer, aligned, high, space⟩ := window
  have incBound : capBoundaryIncrement marked control ≤
      32 * (1022 - capControlRank control) := by
    by_cases done : control = .done
    · subst control
      simp [capBoundaryIncrement]
    · have rank := cap_control_rank_before_done control valid done
      have inc := cap_boundary_increment_bound marked control
      omega
  have currentBound : cursor < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have nextBound : cursor + capBoundaryIncrement marked control < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  rw [cap_boundary_increment_length] at nextBound
  rw [cap_dfs_open_cursor_effect marked control state next cursor pointer reached, pointer]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt currentBound,
    Nat.mod_eq_of_lt nextBound, cap_boundary_increment_length]

theorem cap_open_step_head_slot (marked : Nat → Bool) (control : CapDfsControl)
    (state next reference : MachineState) (rootBase limit floor : Nat)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (heapBelow : rootBase + 16384 ≤ floor)
    (reached : next ∈ support (capDfsStep false marked control state))
    (ordinal node : Nat)
    (selected : (capControlBoundaryHead marked control)[ordinal]? = some node) :
    readBuffer next ((state.getReg .x25).toNat + 32*ordinal) 32 =
      readBuffer reference (rootBase + 32*node) 32 := by
  cases control with
  | advance atNode => simp [capControlBoundaryHead] at selected
  | done => simp [capControlBoundaryHead] at selected
  | visit atNode =>
      by_cases present : marked atNode = true
      · simp [capControlBoundaryHead, present] at selected
      · have absent : marked atNode = false := Bool.eq_false_iff.mpr present
        simp only [capControlBoundaryHead, absent, Bool.false_eq_true,
          ↓reduceIte] at selected
        have eqs : ordinal = 0 ∧ atNode = node := by
          cases ordinal with
          | zero => simpa using selected
          | succ ordinal => simp at selected
        obtain ⟨rfl, rfl⟩ := eqs
        simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
        subst next
        obtain ⟨cursor, pointer, aligned, high, space⟩ := ready.machine.cursor
        have rank := cap_control_rank_before_done (.visit atNode) ready.machine.valid
          (by intro impossible; cases impossible)
        have cursorBound : cursor + 32 < 2^64 := by
          simp only [MEMORY_BYTES] at limitBound
          omega
        have current : (state.getReg .x25).toNat = cursor := by
          rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have before : floor ≤ cursor := by simpa only [current] using ready.cursorFloor
        have nodeBound : atNode < 512 := ready.machine.valid.2
        simpa only [current, Nat.mul_zero, Nat.add_zero] using
          cap_unknown_open_reference_digest state reference atNode rootBase cursor floor
            ready.machine.stable.roots ready.machine.physical.2 pointer rootAligned aligned
            (by omega) before (by omega) ready.inputFrame

theorem cap_open_run_slots (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (heapBelow : rootBase + 16384 ≤ floor)
    (count : Nat) (control : CapDfsControl) (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (reached : final ∈ support (capDfsRun false marked count control state))
    (ordinal node : Nat)
    (selected : (capControlBoundaries marked count control)[ordinal]? = some node) :
    readBuffer final ((state.getReg .x25).toNat + 32*ordinal) 32 =
      readBuffer reference (rootBase + 32*node) 32 := by
  induction count generalizing control state ordinal with
  | zero => simp [capControlBoundaries] at selected
  | succ count ih =>
      rw [capDfsRun] at reached
      obtain ⟨next, first, tail⟩ := mem_support_bind_peel _ _ reached
      have nextReady := cap_open_read_ready_transport marked rootBase limit floor reference
        limitBound rootBound rootAligned control state ready next first
      have cursor := cap_open_step_cursor_nat marked control state next limit
        ready.machine.valid ready.machine.cursor limitBound first
      rw [capControlBoundaries] at selected
      by_cases inHead : ordinal < (capControlBoundaryHead marked control).length
      · rw [List.getElem?_append_left inHead] at selected
        have emitted := cap_open_step_head_slot marked control state next reference
          rootBase limit floor ready limitBound rootAligned heapBelow first ordinal node selected
        have selfReady : CapOpenReadReady marked rootBase limit
            (next.getReg .x25).toNat next (capControlStep marked control) next :=
          ⟨nextReady.machine, Nat.le_refl _, by intro address below; rfl⟩
        have preserved := cap_open_future_digest marked rootBase limit
          (next.getReg .x25).toNat next limitBound rootBound rootAligned count
          (capControlStep marked control) next final selfReady tail
          ((state.getReg .x25).toNat + 32*ordinal) (by omega)
        exact preserved.trans emitted
      · have after : (capControlBoundaryHead marked control).length ≤ ordinal := by omega
        rw [List.getElem?_append_right after] at selected
        have result := ih (capControlStep marked control) next nextReady tail
          (ordinal - (capControlBoundaryHead marked control).length) selected
        have address : (next.getReg .x25).toNat +
            32*(ordinal - (capControlBoundaryHead marked control).length) =
            (state.getReg .x25).toNat + 32*ordinal := by omega
        simpa only [address] using result

end CommitGolfCandidate
