import CommitGolfCandidate.CapFlow

/-! After reading a nonzero occupancy mark, the actual BLTU distinguishes
internal nodes from known leaves. Internal nodes descend and jump to visit;
known leaves jump to advance. This decision contains no memory accesses or
queries, and its two/three instruction charges exclude the preceding visit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capKnownLeafRegister (checking : Bool) : Reg := if checking then .x19 else .x29
def capKnownEntry (checking : Bool) : Word := if checking then 4620 else 4436
def capKnownAdvance (checking : Bool) : Word := if checking then 4688 else 4496
def capKnownVisit (checking : Bool) : Word := if checking then 4604 else 4420
def capKnownTest (checking : Bool) : CapFlow :=
  .below .x20 (capKnownLeafRegister checking) 8
def capKnownSkip (checking : Bool) : CapFlow := .jump (if checking then 64 else 56)

def capKnownState (checking : Bool) (state : MachineState) (node : Nat) : MachineState :=
  let tested := capFlowState (capKnownTest checking) state
  if node < 128 then
    capFlowState (.jump 2097124) (capNavigationState .descend tested)
  else capFlowState (capKnownSkip checking) tested

private theorem below_known (checking : Bool) (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (leaves : state.getReg (capKnownLeafRegister checking) = 128)
    (bounded : node < 256) :
    state.getReg .x20 < state.getReg (capKnownLeafRegister checking) ↔ node < 128 := by
  rw [index, leaves, BitVec.lt_def]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : node < 2^64)]
  rfl

theorem cap_known_test_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (leaves : state.getReg (capKnownLeafRegister checking) = 128)
    (bounded : node < 256) :
    (capFlowState (capKnownTest checking) state).pc =
      if node < 128 then capNavigationPC checking .descend
      else capKnownEntry checking + 4 := by
  unfold capKnownTest
  rw [cap_flow_below_pc]
  simp only [below_known checking state node index leaves bounded, pc]
  cases checking <;> split <;> rfl

theorem cap_known_state_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (leaves : state.getReg (capKnownLeafRegister checking) = 128)
    (bounded : node < 256) :
    (capKnownState checking state node).pc =
      if node < 128 then capKnownVisit checking else capKnownAdvance checking := by
  unfold capKnownState
  by_cases internal : node < 128
  · simp only [if_pos internal]
    rw [cap_flow_jump_pc, cap_navigation_pc,
      cap_known_test_pc checking state node pc index leaves bounded, if_pos internal]
    cases checking <;> rfl
  · simp only [if_neg internal]
    unfold capKnownSkip
    rw [cap_flow_jump_pc, cap_known_test_pc checking state node pc index leaves bounded,
      if_neg internal]
    cases checking <;> rfl

theorem cap_known_state_node (checking : Bool) (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capKnownState checking state node).getReg .x20 =
      BitVec.ofNat 64 (if node < 128 then 2 * node else node) := by
  unfold capKnownState
  by_cases internal : node < 128
  · simp only [if_pos internal]
    rw [cap_flow_register, cap_navigation_descend]
    exact (cap_flow_register _ _ _).trans index
  · simp only [if_neg internal]
    rw [cap_flow_register, cap_flow_register, index]

theorem cap_known_state_memory (checking : Bool) (state : MachineState) (node : Nat) :
    (capKnownState checking state node).mem = state.mem := by
  unfold capKnownState
  split <;> simp only [cap_flow_memory, cap_navigation_memory]

theorem cap_known_state_register (checking : Bool) (state : MachineState) (node : Nat)
    (reg : Reg) (outside : reg ≠ .x20 ∧ reg ≠ .x7) :
    (capKnownState checking state node).getReg reg = state.getReg reg := by
  unfold capKnownState
  split <;> simp only [cap_flow_register, cap_navigation_register _ _ reg outside]

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_known_decision_execute (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (leaves : state.getReg (capKnownLeafRegister checking) = 128)
    (bounded : node < 256) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) ((if node < 128 then 3 else 2) + fuel)
        state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capKnownState checking state node) allowCoins
          return result.charge (if node < 128 then 3 else 2) 0) := by
  let tested := capFlowState (capKnownTest checking) state
  have fetched : fetch (capWalkImage checking) state =
      some (.base (capFlowInstruction (capKnownTest checking))) := by
    cases checking
    · apply cap_image_fetch _ state 85 _ (by decide) pc
      rfl
    · apply cap_image_fetch _ state 131 _ (by decide) pc
      rfl
  have testedPC := cap_known_test_pc checking state node pc index leaves bounded
  by_cases internal : node < 128
  · simp only [if_pos internal] at testedPC ⊢
    have back : fetch (capWalkImage checking) (capNavigationState .descend tested) =
        some (.base (capFlowInstruction (.jump 2097124))) := by
      cases checking
      · apply cap_image_fetch _ (capNavigationState .descend tested) 88 _ (by decide)
        · rw [cap_navigation_pc, testedPC]
          rfl
        · rfl
      · apply cap_image_fetch _ (capNavigationState .descend tested) 134 _ (by decide)
        · rw [cap_navigation_pc, testedPC]
          rfl
        · rfl
    rw [show 3 + fuel = 1 + (1 + (1 + fuel)) by omega,
      cap_flow_execute _ _ state fetched,
      cap_navigation_image_execute checking .descend tested testedPC,
      cap_flow_execute _ _ _ back]
    simp only [bind_assoc, pure_bind, charge_pair, capKnownState, if_pos internal]
    rfl
  · simp only [if_neg internal] at testedPC ⊢
    have skip : fetch (capWalkImage checking) tested =
        some (.base (capFlowInstruction (capKnownSkip checking))) := by
      cases checking
      · apply cap_image_fetch _ tested 86 _ (by decide)
        · rw [testedPC]
          rfl
        · rfl
      · apply cap_image_fetch _ tested 132 _ (by decide)
        · rw [testedPC]
          rfl
        · rfl
    rw [show 2 + fuel = 1 + (1 + fuel) by omega,
      cap_flow_execute _ _ state fetched, cap_flow_execute _ _ tested skip]
    simp only [bind_assoc, pure_bind, charge_pair, capKnownState, if_neg internal]
    rfl

end CommitGolfCandidate
