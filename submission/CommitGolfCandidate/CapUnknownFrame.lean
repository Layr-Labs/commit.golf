import CommitGolfCandidate.CapUnknownVisit

/-! Control and occupancy frames for complete unknown visits. Successful
copies advance exactly one digest while retaining the DFS node and selectors.
Short checker input retains memory and the original cursor at rejection. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_unknown_check_guard_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23) :
    (capUnknownCheckGuard state).getReg reg = state.getReg reg := by
  rw [capUnknownCheckGuard, cap_boundary_guard_register _ reg outside.1]
  exact cap_marked_prepare_register true state reg outside

theorem cap_unknown_check_guard_memory (state : MachineState) :
    (capUnknownCheckGuard state).mem = state.mem := by
  rw [capUnknownCheckGuard, cap_boundary_guard_memory, cap_marked_prepare_memory]

theorem cap_unknown_open_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x25) :
    (capUnknownOpenState state).getReg reg = state.getReg reg := by
  rw [capUnknownOpenState, cap_boundary_state_register false _ reg outside]
  exact cap_marked_prepare_register false state reg ⟨outside.1, outside.2.1, outside.2.2.1⟩

theorem cap_unknown_check_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x25) :
    (capUnknownCheckState state).getReg reg = state.getReg reg := by
  rw [capUnknownCheckState, cap_boundary_state_register true _ reg outside]
  exact cap_unknown_check_guard_register state reg ⟨outside.1, outside.2.1, outside.2.2.1⟩

theorem cap_unknown_open_cursor (state : MachineState) (cursor : Nat)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor) :
    (capUnknownOpenState state).getReg .x25 = BitVec.ofNat 64 (cursor + 32) := by
  apply cap_boundary_state_cursor
  exact (cap_marked_prepare_register false state .x25 (by decide)).trans proof

theorem cap_unknown_check_cursor (state : MachineState) (cursor : Nat)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor) :
    (capUnknownCheckState state).getReg .x25 = BitVec.ofNat 64 (cursor + 32) := by
  apply cap_boundary_state_cursor
  exact (cap_unknown_check_guard_register state .x25 (by decide)).trans proof

theorem cap_unknown_open_pc (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit false)
    (marks : state.getReg .x22 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 512)
    (marked : Nat → Bool) (ready : CapMarksReady state 256 0 marked)
    (absent : marked node = false) :
    (capUnknownOpenState state).pc = capAdvanceEntry false :=
  cap_boundary_state_pc false _ (cap_unknown_prepare_pc false state node pc marks
    index positive bounded marked ready absent)

theorem cap_unknown_check_pc (state : MachineState) (node cursor limit : Nat)
    (pc : state.pc = capKnownVisit true)
    (marks : state.getReg .x9 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 512)
    (marked : Nat → Bool) (ready : CapMarksReady state 256 0 marked)
    (absent : marked node = false)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (noWrap : cursor + 32 < 2^64) (limitBound : limit < 2^64)
    (enough : cursor + 32 ≤ limit) :
    (capUnknownCheckState state).pc = capAdvanceEntry true := by
  apply cap_boundary_state_pc true _
  have next := cap_unknown_check_guard_pc state node cursor limit pc marks index
    positive bounded marked ready absent proof proofEnd noWrap limitBound
  simpa only [if_pos enough] using next

theorem cap_unknown_open_marks (state : MachineState) (node rootBase cursor : Nat)
    (marked : Nat → Bool)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorBound : cursor + 32 ≤ 2^64) (high : 32768 ≤ cursor)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capUnknownOpenState state) 256 0 marked := by
  apply cap_boundary_marks_ready false _ node rootBase cursor marked
    ((cap_marked_prepare_register false state .x9 (by decide)).trans roots)
    ((cap_marked_prepare_register false state .x20 (by decide)).trans index)
    ((cap_marked_prepare_register false state .x25 (by decide)).trans proof)
    cursorBound (Or.inr high)
  exact cap_marks_ready_memory state (capMarkedPrepare false state) 256 0 marked
    (cap_marked_prepare_memory false state) ready

theorem cap_unknown_check_marks (state : MachineState) (node cursor : Nat)
    (marked : Nat → Bool) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capUnknownCheckState state) 256 0 marked := by
  apply cap_boundary_marks_ready true _ node 12288 cursor marked
    ((cap_unknown_check_guard_register state .x18 (by decide)).trans roots)
    ((cap_unknown_check_guard_register state .x20 (by decide)).trans index)
    ((cap_unknown_check_guard_register state .x25 (by decide)).trans proof)
    (by simp only [capBoundaryDestination, ↓reduceIte]; omega)
    (Or.inl (by simp only [capBoundaryDestination, ↓reduceIte]; omega))
  exact cap_marks_ready_memory state (capUnknownCheckGuard state) 256 0 marked
    (cap_unknown_check_guard_memory state) ready

theorem cap_unknown_check_high (state reference : MachineState) (node cursor : Nat)
    (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capUnknownCheckState state) reference := by
  apply cap_boundary_high_bytes true _ reference node 12288 cursor
    ((cap_unknown_check_guard_register state .x18 (by decide)).trans roots)
    ((cap_unknown_check_guard_register state .x20 (by decide)).trans index)
    ((cap_unknown_check_guard_register state .x25 (by decide)).trans proof)
  · simp only [capBoundaryDestination, ↓reduceIte]
    omega
  · simp only [capBoundaryDestination, ↓reduceIte]
    omega
  · exact cap_high_bytes_memory state (capUnknownCheckGuard state) reference
      (cap_unknown_check_guard_memory state) frame

end CommitGolfCandidate
