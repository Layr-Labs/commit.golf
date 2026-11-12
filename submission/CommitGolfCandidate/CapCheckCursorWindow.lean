import CommitGolfCandidate.CapCheckCursorEffect

/-! A bounded checker proof cursor. Unlike the opening window, this does not
reserve space for all future boundary nodes. Each successful unknown visit
must satisfy its actual end-pointer guard; otherwise the machine rejects
before loading a proof word. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

structure CapCheckCursorWindow (limit : Nat) (state : MachineState) : Prop where
  aligned : (state.getReg .x25).toNat % 8 = 0
  beforeEnd : (state.getReg .x25).toNat ≤ limit
  endPointer : state.getReg .x22 = BitVec.ofNat 64 limit
  limitBound : limit ≤ MEMORY_BYTES

theorem cap_check_cursor_window_transport (marked : Nat → Bool)
    (control : CapDfsControl) (state next : MachineState) (limit : Nat)
    (window : CapCheckCursorWindow limit state)
    (space : (state.getReg .x25).toNat + capBoundaryIncrement marked control ≤ limit)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    CapCheckCursorWindow limit next := by
  have pointer : state.getReg .x25 = BitVec.ofNat 64 (state.getReg .x25).toNat :=
    by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have effect := cap_dfs_check_cursor_effect marked control state next
    (state.getReg .x25).toNat pointer reached
  have small : (state.getReg .x25).toNat + capBoundaryIncrement marked control < 2^64 := by
    have bound := window.limitBound
    simp only [MEMORY_BYTES] at bound
    omega
  have numeric := congrArg BitVec.toNat effect
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
  refine ⟨?_,?_,?_,window.limitBound⟩
  · have aligned := cap_boundary_increment_aligned marked control
    have original := window.aligned
    rw [numeric]
    omega
  · rw [numeric]
    exact space
  · exact (cap_dfs_check_end_pointer marked control state next reached).trans window.endPointer

theorem cap_check_cursor_no_wrap (limit : Nat) (state : MachineState)
    (window : CapCheckCursorWindow limit state) :
    (state.getReg .x25).toNat + 32 < 2^64 ∧ limit < 2^64 := by
  have bounded := window.limitBound
  have beforeEnd := window.beforeEnd
  simp only [MEMORY_BYTES] at bounded
  omega

def capCheckBoundaryEnough (marked : Nat → Bool) (control : CapDfsControl)
    (state : MachineState) : Prop :=
  ∀ node, control = .visit node → marked node = false →
    (state.getReg .x25).toNat + 32 ≤ (state.getReg .x22).toNat

theorem cap_check_cursor_space (marked : Nat → Bool) (control : CapDfsControl)
    (state : MachineState) (limit : Nat) (window : CapCheckCursorWindow limit state)
    (enough : capCheckBoundaryEnough marked control state) :
    (state.getReg .x25).toNat + capBoundaryIncrement marked control ≤ limit := by
  have small := cap_check_cursor_no_wrap limit state window
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capBoundaryIncrement,present,↓reduceIte,Nat.add_zero]
        exact window.beforeEnd
      · have absent := Bool.eq_false_iff.mpr present
        have accepted := enough node rfl absent
        rw [window.endPointer] at accepted
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small.2] at accepted
        simpa only [capBoundaryIncrement,absent,Bool.false_eq_true,↓reduceIte] using accepted
  | advance node =>
      simpa only [capBoundaryIncrement,Nat.add_zero] using window.beforeEnd
  | done =>
      simpa only [capBoundaryIncrement,Nat.add_zero] using window.beforeEnd

/-- Successful-copy admission follows from the real guard and cursor window,
without requiring the whole remaining proof in advance. -/
def cap_check_boundary_ready (marked : Nat → Bool) (control : CapDfsControl)
    (state : MachineState) (limit : Nat) (window : CapCheckCursorWindow limit state)
    (enough : capCheckBoundaryEnough marked control state)
    (node : Nat) (atNode : control = .visit node) (absent : marked node = false)
    (bounded : node < 512) : CapDfsBoundaryReady true state 12288 node := by
  have small := cap_check_cursor_no_wrap limit state window
  have space := cap_check_cursor_space marked control state limit window enough
  simp only [atNode,capBoundaryIncrement,absent,Bool.false_eq_true,↓reduceIte] at space
  refine {
    cursor := (state.getReg .x25).toNat
    pointer := by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    aligned := window.aligned
    bound := space.trans window.limitBound
    rootBound := ?_
    rootAligned := by decide
    limit := limit
    proofEnd := fun _ => window.endPointer
    limitBound := fun _ => window.limitBound
    enough := fun _ => space
    highOutput := ?_
  }
  · simp only [MEMORY_BYTES]
    omega
  · intro impossible
    contradiction

end CommitGolfCandidate
