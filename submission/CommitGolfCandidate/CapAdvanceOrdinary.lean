import CommitGolfCandidate.CapAdvanceGuard
import CommitGolfCandidate.CapKnownDecision

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capAdvanceSiblingJump (checking : Bool) : CapFlow :=
  .jump (if checking then 2097024 else 2097052)
def capAdvanceSiblingState (checking : Bool) (state : MachineState) : MachineState :=
  capFlowState (capAdvanceSiblingJump checking)
    (capNavigationState .sibling (capAdvanceGuardState checking state))
def capAdvanceOpenAscentState (state : MachineState) : MachineState :=
  capFlowState (.jump 2097136)
    (capNavigationState .ascend (capAdvanceGuardState false state))

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_advance_sibling_execute (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (even : node % 2 = 0) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (5 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capAdvanceSiblingState checking state) allowCoins
          return result.charge 5 0) := by
  have guardPC := cap_advance_guard_pc checking state node pc index root bounded nonroot
  simp only [even, if_pos rfl] at guardPC
  have back : fetch (capWalkImage checking)
      (capNavigationState .sibling (capAdvanceGuardState checking state)) =
        some (.base (capFlowInstruction (capAdvanceSiblingJump checking))) := by
    cases checking
    · apply cap_image_fetch _ _ 106 _ (by decide)
      · rw [cap_navigation_pc, guardPC]
        rfl
      · rfl
    · apply cap_image_fetch _ _ 159 _ (by decide)
      · rw [cap_navigation_pc, guardPC]
        rfl
      · rfl
  rw [show 5 + fuel = 3 + (1 + (1 + fuel)) by omega,
    cap_advance_guard_execute checking state node pc index root bounded nonroot,
    cap_navigation_image_execute checking .sibling _ guardPC,
    cap_flow_execute _ _ _ back]
  simp only [bind_assoc, pure_bind, charge_pair, capAdvanceSiblingState]

theorem cap_advance_sibling_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (even : node % 2 = 0) :
    (capAdvanceSiblingState checking state).pc = capKnownVisit checking := by
  have guardPC := cap_advance_guard_pc checking state node pc index root bounded nonroot
  simp only [even, if_pos rfl] at guardPC
  unfold capAdvanceSiblingState capAdvanceSiblingJump
  rw [cap_flow_jump_pc, cap_navigation_pc, guardPC]
  cases checking <;> rfl

theorem cap_advance_sibling_node (checking : Bool) (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capAdvanceSiblingState checking state).getReg .x20 = BitVec.ofNat 64 (node + 1) := by
  rw [capAdvanceSiblingState, cap_flow_register]
  apply cap_navigation_sibling
  exact (cap_advance_guard_register checking state .x20 (by decide)).trans index

theorem cap_advance_sibling_memory (checking : Bool) (state : MachineState) :
    (capAdvanceSiblingState checking state).mem = state.mem := by
  rw [capAdvanceSiblingState, cap_flow_memory, cap_navigation_memory,
    cap_advance_guard_memory]

theorem cap_advance_open_ascent_execute (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry false)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (odd : node % 2 ≠ 0) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage false) (5 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage false) fuel
            (capAdvanceOpenAscentState state) allowCoins
          return result.charge 5 0) := by
  have guardPC := cap_advance_guard_pc false state node pc index root bounded nonroot
  simp only [if_neg odd] at guardPC
  have back : fetch (capWalkImage false)
      (capNavigationState .ascend (capAdvanceGuardState false state)) =
        some (.base (capFlowInstruction (.jump 2097136))) := by
    apply cap_image_fetch _ _ 104 _ (by decide)
    · rw [cap_navigation_pc, guardPC]
      rfl
    · rfl
  rw [show 5 + fuel = 3 + (1 + (1 + fuel)) by omega,
    cap_advance_guard_execute false state node pc index root bounded nonroot,
    cap_navigation_image_execute false .ascend _ guardPC,
    cap_flow_execute _ _ _ back]
  simp only [bind_assoc, pure_bind, charge_pair, capAdvanceOpenAscentState]

theorem cap_advance_open_ascent_pc (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry false)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (odd : node % 2 ≠ 0) :
    (capAdvanceOpenAscentState state).pc = capAdvanceEntry false := by
  have guardPC := cap_advance_guard_pc false state node pc index root bounded nonroot
  simp only [if_neg odd] at guardPC
  rw [capAdvanceOpenAscentState, cap_flow_jump_pc, cap_navigation_pc, guardPC]
  rfl

theorem cap_advance_open_ascent_node (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capAdvanceOpenAscentState state).getReg .x20 = BitVec.ofNat 64 (node / 2) := by
  rw [capAdvanceOpenAscentState, cap_flow_register]
  apply cap_navigation_ascend _ node _ bounded
  exact (cap_advance_guard_register false state .x20 (by decide)).trans index

theorem cap_advance_open_ascent_memory (state : MachineState) :
    (capAdvanceOpenAscentState state).mem = state.mem := by
  rw [capAdvanceOpenAscentState, cap_flow_memory, cap_navigation_memory,
    cap_advance_guard_memory]

end CommitGolfCandidate
