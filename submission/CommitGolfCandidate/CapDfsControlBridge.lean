import CommitGolfCandidate.CapDfsControl
import CommitGolfCandidate.CapUnknownFrame
import CommitGolfCandidate.CapAdvanceOrdinary
import CommitGolfCandidate.CapCheckAscent

/-! The logical DFS node and phase are realized by the actual PC and x20.
These bridges identify every successful macro with the structural control
step. Checker replies are unrestricted; early short-proof rejection is
handled separately from successful advance. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapDfsStateControl (checking : Bool) (state : MachineState) :
    CapDfsControl → Prop
  | .visit node => state.pc = capKnownVisit checking ∧
      state.getReg .x20 = BitVec.ofNat 64 node
  | .advance node => state.pc = capAdvanceEntry checking ∧
      state.getReg .x20 = BitVec.ofNat 64 node
  | .done => state.pc = capAdvanceDone checking

theorem cap_dfs_marked_control (checking : Bool) (state : MachineState)
    (node : Nat) (marked : Nat → Bool)
    (control : CapDfsStateControl checking state (.visit node))
    (valid : CapDfsControlValid (.visit node))
    (marks : state.getReg (capVisitMarks checking) = 28672)
    (leaves : state.getReg (capKnownLeafRegister checking) = 256)
    (ready : CapMarksReady state 256 0 marked) (present : marked node = true) :
    CapDfsStateControl checking (capMarkedVisitState checking state node)
      (capControlStep marked (.visit node)) := by
  have preparedPC := cap_marked_prepare_pc checking state node control.1 marks control.2
    valid.1 valid.2 marked ready present
  have nextPC := cap_known_state_pc checking (capMarkedPrepare checking state) node
    preparedPC
    ((cap_marked_prepare_register checking state .x20 (by decide)).trans control.2)
    (by
      rw [cap_marked_prepare_register]
      · exact leaves
      · cases checking <;> decide) valid.2
  have nextIndex := cap_marked_visit_node checking state node control.2
  simp only [capControlStep, present, Bool.true_and, decide_eq_true_eq]
  by_cases internal : node < 256
  · simp only [if_pos internal] at nextPC nextIndex ⊢
    exact ⟨nextPC, nextIndex⟩
  · simp only [if_neg internal] at nextPC nextIndex ⊢
    exact ⟨nextPC, nextIndex⟩

theorem cap_dfs_unknown_open_control (state : MachineState) (node : Nat)
    (marked : Nat → Bool)
    (control : CapDfsStateControl false state (.visit node))
    (valid : CapDfsControlValid (.visit node))
    (marks : state.getReg .x22 = 28672)
    (ready : CapMarksReady state 256 0 marked) (absent : marked node = false) :
    CapDfsStateControl false (capUnknownOpenState state)
      (capControlStep marked (.visit node)) := by
  simp only [capControlStep, absent, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact ⟨cap_unknown_open_pc state node control.1 marks control.2 valid.1 valid.2
      marked ready absent,
    (cap_unknown_open_register state .x20 (by decide)).trans control.2⟩

theorem cap_dfs_unknown_check_control (state : MachineState) (node cursor limit : Nat)
    (marked : Nat → Bool)
    (control : CapDfsStateControl true state (.visit node))
    (valid : CapDfsControlValid (.visit node))
    (marks : state.getReg .x9 = 28672)
    (ready : CapMarksReady state 256 0 marked) (absent : marked node = false)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (noWrap : cursor + 32 < 2^64) (limitBound : limit < 2^64)
    (enough : cursor + 32 ≤ limit) :
    CapDfsStateControl true (capUnknownCheckState state)
      (capControlStep marked (.visit node)) := by
  simp only [capControlStep, absent, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  exact ⟨cap_unknown_check_pc state node cursor limit control.1 marks control.2 valid.1
      valid.2 marked ready absent proof proofEnd noWrap limitBound enough,
    (cap_unknown_check_register state .x20 (by decide)).trans control.2⟩

theorem cap_dfs_sibling_control (checking : Bool) (state : MachineState) (node : Nat)
    (marked : Nat → Bool)
    (control : CapDfsStateControl checking state (.advance node))
    (valid : CapDfsControlValid (.advance node))
    (root : state.getReg .x31 = 1) (nonroot : node ≠ 1) (even : node % 2 = 0) :
    CapDfsStateControl checking (capAdvanceSiblingState checking state)
      (capControlStep marked (.advance node)) := by
  simp only [capControlStep, if_neg nonroot, if_pos even]
  exact ⟨cap_advance_sibling_pc checking state node control.1 control.2 root valid.2
      nonroot even, cap_advance_sibling_node checking state node control.2⟩

theorem cap_dfs_open_ascent_control (state : MachineState) (node : Nat)
    (marked : Nat → Bool)
    (control : CapDfsStateControl false state (.advance node))
    (valid : CapDfsControlValid (.advance node))
    (root : state.getReg .x31 = 1) (nonroot : node ≠ 1) (odd : node % 2 ≠ 0) :
    CapDfsStateControl false (capAdvanceOpenAscentState state)
      (capControlStep marked (.advance node)) := by
  simp only [capControlStep, if_neg nonroot, if_neg odd]
  exact ⟨cap_advance_open_ascent_pc state node control.1 control.2 root valid.2
      nonroot odd, cap_advance_open_ascent_node state node control.2 valid.2⟩

theorem cap_dfs_check_ascent_control (state : MachineState) (node : Nat)
    (marked : Nat → Bool) (answer : BitVec 256)
    (control : CapDfsStateControl true state (.advance node))
    (valid : CapDfsControlValid (.advance node))
    (root : state.getReg .x31 = 1) (nonroot : node ≠ 1) (odd : node % 2 ≠ 0) :
    CapDfsStateControl true (capCheckAscentAnswer state answer)
      (capControlStep marked (.advance node)) := by
  simp only [capControlStep, if_neg nonroot, if_neg odd]
  exact ⟨cap_check_ascent_answer_pc state answer
      (cap_check_ascent_prepared_pc state node control.1 control.2 root valid.2 nonroot odd),
    cap_check_ascent_answer_index state answer node control.2 valid.2⟩

theorem cap_dfs_root_control (checking : Bool) (state : MachineState)
    (marked : Nat → Bool)
    (control : CapDfsStateControl checking state (.advance 1))
    (root : state.getReg .x31 = 1) :
    CapDfsStateControl checking (capAdvanceRootState checking state)
      (capControlStep marked (.advance 1)) := by
  exact cap_advance_root_pc checking state 1 control.1 control.2 root (by decide)

end CommitGolfCandidate
