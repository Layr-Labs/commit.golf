import CommitGolfCandidate.CapDfsControlBridge

/-! Stable selectors and workspace bases throughout cap traversal. Scratch,
node, cursor and syscall-address registers may change. The invariant retains
the opening's supplied trapdoor base instead of identifying it with the
checker's fixed low root heap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

structure CapDfsStable (checking : Bool) (state : MachineState) (rootBase : Nat) : Prop where
  marks : state.getReg (capVisitMarks checking) = 28672
  roots : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase
  leaves : state.getReg (capKnownLeafRegister checking) = 256
  root : state.getReg .x31 = 1
  selectors : checking = true →
    state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0

abbrev CapDfsPreserved (reg : Reg) : Prop :=
  reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧
    reg ≠ .x25 ∧ reg ≠ .x10 ∧ reg ≠ .x12

theorem cap_dfs_stable_transport (checking : Bool) (state next : MachineState)
    (rootBase : Nat) (stable : CapDfsStable checking state rootBase)
    (frame : ∀ reg, CapDfsPreserved reg → next.getReg reg = state.getReg reg) :
    CapDfsStable checking next rootBase := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [frame _ (by cases checking <;> decide)]
    exact stable.marks
  · rw [frame _ (by cases checking <;> decide)]
    exact stable.roots
  · rw [frame _ (by cases checking <;> decide)]
    exact stable.leaves
  · rw [frame .x31 (by decide)]
    exact stable.root
  · intro active
    rw [frame .x5 (by decide), frame .x11 (by decide), frame .x13 (by decide)]
    exact stable.selectors active

theorem cap_dfs_marked_register (checking : Bool) (state : MachineState)
    (node : Nat) (reg : Reg) (outside : CapDfsPreserved reg) :
    (capMarkedVisitState checking state node).getReg reg = state.getReg reg := by
  rw [capMarkedVisitState,
    cap_known_state_register checking _ node reg ⟨outside.2.2.1, outside.2.1⟩]
  exact cap_marked_prepare_register checking state reg
    ⟨outside.1, outside.2.1, outside.2.2.2.1⟩

theorem cap_dfs_sibling_register (checking : Bool) (state : MachineState)
    (reg : Reg) (outside : CapDfsPreserved reg) :
    (capAdvanceSiblingState checking state).getReg reg = state.getReg reg := by
  rw [capAdvanceSiblingState, cap_flow_register,
    cap_navigation_register _ _ reg ⟨outside.2.2.1, outside.2.1⟩]
  exact cap_advance_guard_register checking state reg outside.2.1

theorem cap_dfs_open_ascent_register (state : MachineState)
    (reg : Reg) (outside : CapDfsPreserved reg) :
    (capAdvanceOpenAscentState state).getReg reg = state.getReg reg := by
  rw [capAdvanceOpenAscentState, cap_flow_register,
    cap_navigation_register _ _ reg ⟨outside.2.2.1, outside.2.1⟩]
  exact cap_advance_guard_register false state reg outside.2.1

theorem cap_dfs_check_ascent_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : CapDfsPreserved reg) :
    (capCheckAscentAnswer state answer).getReg reg = state.getReg reg :=
  cap_check_ascent_answer_register state answer reg
    ⟨outside.2.1, outside.2.2.1, outside.2.2.2.2.2.1, outside.2.2.2.2.2.2⟩

theorem cap_dfs_marked_stable (checking : Bool) (state : MachineState)
    (node rootBase : Nat) (stable : CapDfsStable checking state rootBase) :
    CapDfsStable checking (capMarkedVisitState checking state node) rootBase :=
  cap_dfs_stable_transport checking state _ rootBase stable
    (cap_dfs_marked_register checking state node)

theorem cap_dfs_sibling_stable (checking : Bool) (state : MachineState)
    (rootBase : Nat) (stable : CapDfsStable checking state rootBase) :
    CapDfsStable checking (capAdvanceSiblingState checking state) rootBase :=
  cap_dfs_stable_transport checking state _ rootBase stable
    (cap_dfs_sibling_register checking state)

theorem cap_dfs_open_ascent_stable (state : MachineState)
    (rootBase : Nat) (stable : CapDfsStable false state rootBase) :
    CapDfsStable false (capAdvanceOpenAscentState state) rootBase :=
  cap_dfs_stable_transport false state _ rootBase stable
    (cap_dfs_open_ascent_register state)

theorem cap_dfs_check_ascent_stable (state : MachineState) (answer : BitVec 256)
    (rootBase : Nat) (stable : CapDfsStable true state rootBase) :
    CapDfsStable true (capCheckAscentAnswer state answer) rootBase :=
  cap_dfs_stable_transport true state _ rootBase stable
    (cap_dfs_check_ascent_register state answer)

theorem cap_dfs_unknown_open_stable (state : MachineState)
    (rootBase : Nat) (stable : CapDfsStable false state rootBase) :
    CapDfsStable false (capUnknownOpenState state) rootBase := by
  apply cap_dfs_stable_transport false state _ rootBase stable
  intro reg outside
  exact cap_unknown_open_register state reg
    ⟨outside.1, outside.2.1, outside.2.2.2.1, outside.2.2.2.2.1⟩

theorem cap_dfs_unknown_check_stable (state : MachineState)
    (rootBase : Nat) (stable : CapDfsStable true state rootBase) :
    CapDfsStable true (capUnknownCheckState state) rootBase := by
  apply cap_dfs_stable_transport true state _ rootBase stable
  intro reg outside
  exact cap_unknown_check_register state reg
    ⟨outside.1, outside.2.1, outside.2.2.2.1, outside.2.2.2.2.1⟩

end CommitGolfCandidate
