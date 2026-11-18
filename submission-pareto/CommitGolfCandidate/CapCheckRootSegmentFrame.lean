import CommitGolfCandidate.CapDfsRootFootprint
import CommitGolfCandidate.CapCheckSegmentSuccess

/-! The actual root-heap frame follows the control segment's write footprint.
In particular, a right subtree cannot overwrite its completed left sibling.
Only successful phase results are used; arbitrary initial parent roots need
not satisfy any compression equation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_root_step_frame (compress : Compression) (marked : Nat → Bool)
    (control : CapDfsControl) (roots : Nat → Digest) (boundary : Digest)
    (other : Nat) (outside : other ∉ capControlRootWritesHead marked control) :
    capCheckRootStep compress marked control roots boundary other=roots other := by
  cases control with
  | visit node =>
    by_cases present : marked node=true
    · simp only [capCheckRootStep,if_pos present]
    · simp only [capControlRootWritesHead,if_neg present,List.mem_singleton] at outside
      simp only [capCheckRootStep,if_neg present,if_neg outside]
  | advance node =>
    by_cases skip : node=1 ∨ node%2=0
    · simp only [capCheckRootStep,if_pos skip]
    · simp only [capControlRootWritesHead,if_neg skip,List.mem_singleton] at outside
      simp only [capCheckRootStep,if_neg skip,if_neg outside]
  | done => rfl

theorem cap_check_value_root_frame (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state : MachineState) (ready : CapCheckDfsReady limit marked control state)
    (above : 32768≤(state.getReg .x25).toNat)
    (other : Nat) (bounded : other<512)
    (outside : other ∉ capControlRootWrites marked count control)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    capReadRoot (capCheckDfsValue oracle marked count control state).1 other=
      capReadRoot state other := by
  induction count generalizing control state with
  | zero => rfl
  | succ count ih =>
    rw [capCheckDfsValue] at passed ⊢
    cases short : capCheckDfsShort marked control state
    · simp only [short,Bool.false_eq_true,↓reduceIte] at passed ⊢
      have excluded : other ∉ capControlRootWritesHead marked control ∧
          other ∉ capControlRootWrites marked count (capControlStep marked control) := by
        simpa only [capControlRootWrites,List.mem_append,not_or] using outside
      have reached := cap_check_next_supported oracle marked control state
      have nextReady := cap_check_dfs_ready_transport limit marked control state _
        ready short reached
      have progress := cap_check_step_cursor_monotone limit marked control state _
        ready short reached
      have tail := ih (capControlStep marked control)
        (capCheckDfsNext oracle marked control state) nextReady (above.trans progress)
        excluded.2 passed
      have step := cap_check_dfs_next_roots oracle limit marked control state
        ready above other bounded
      rw [cap_check_root_step_frame (s6Compress oracle.compression) marked control _ _
        other excluded.1] at step
      exact tail.trans step
    · simp only [short,↓reduceIte] at passed
      contradiction

theorem cap_check_subtree_root_below (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (height node : Nat) (state : MachineState)
    (lower : 256≤node*2^height) (upper : (node+1)*2^height≤512)
    (ready : CapCheckDfsReady limit marked (.visit node) state)
    (above : 32768≤(state.getReg .x25).toNat)
    (other : Nat) (below : other<node) (bounded : other<512)
    (passed : (capCheckSubtreeValue oracle marked height node state).2=true) :
    capReadRoot (capCheckSubtreeValue oracle marked height node state).1 other=
      capReadRoot state other := by
  have outside : other ∉ capControlRootWrites marked
      (capSubtreeSteps marked height node) (.visit node) := by
    intro member
    have bound := cap_subtree_root_writes_bound marked height node lower upper other member
    omega
  have result := cap_check_value_root_frame oracle limit marked
    (capSubtreeSteps marked height node) (.visit node) state ready above other bounded
    outside (by
      rw [cap_check_subtree_value oracle marked height node state lower upper]
      exact passed)
  rw [cap_check_subtree_value oracle marked height node state lower upper] at result
  exact result

end CommitGolfCandidate
