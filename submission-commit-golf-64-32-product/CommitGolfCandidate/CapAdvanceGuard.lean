import CommitGolfCandidate.CapFlow

/-! Root completion and nonroot parity dispatch for cap DFS. Three actual
instructions distinguish sibling navigation from ascent. The root branch
finishes in one instruction and never executes the parity instructions. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capAdvanceEntry (checking : Bool) : Word := if checking then 4688 else 4496
def capAdvanceDone (checking : Bool) : Word := if checking then 4736 else 4524
def capAdvanceRootFlow (checking : Bool) : CapFlow :=
  .equal .x20 .x31 (if checking then 48 else 28)
def capAdvanceParityFlow (checking : Bool) : CapFlow :=
  .equal .x7 .x0 (if checking then 32 else 12)
def capAdvanceRootState (checking : Bool) (state : MachineState) : MachineState :=
  capFlowState (capAdvanceRootFlow checking) state
def capAdvanceGuardState (checking : Bool) (state : MachineState) : MachineState :=
  capFlowState (capAdvanceParityFlow checking)
    (capNavigationState .parity (capAdvanceRootState checking state))

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

private theorem node_word_one (node : Nat) (bounded : node < 512) :
    BitVec.ofNat 64 node = (1 : Word) ↔ node = 1 := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : node < 2^64),
      show (1 : Word).toNat = 1 by decide] at numeric
    exact numeric
  · intro equal
    subst node
    rfl

theorem cap_advance_root_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) :
    (capAdvanceRootState checking state).pc =
      if node = 1 then capAdvanceDone checking else capNavigationPC checking .parity := by
  unfold capAdvanceRootState capAdvanceRootFlow
  rw [cap_flow_equal_pc]
  simp only [index, root, node_word_one node bounded, pc]
  cases checking <;> split <;> rfl

theorem cap_advance_root_fetched (checking : Bool) (state : MachineState)
    (pc : state.pc = capAdvanceEntry checking) :
    fetch (capWalkImage checking) state =
      some (.base (capFlowInstruction (capAdvanceRootFlow checking))) := by
  cases checking
  · apply cap_image_fetch _ state 100 _ (by decide) pc
    rfl
  · apply cap_image_fetch _ state 148 _ (by decide) pc
    rfl

theorem cap_advance_root_execute (checking : Bool) (state : MachineState)
    (pc : state.pc = capAdvanceEntry checking) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (1 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capAdvanceRootState checking state) allowCoins
          return result.charge 1 0) :=
  cap_flow_execute _ _ state (cap_advance_root_fetched checking state pc) fuel allowCoins

private theorem parity_word_zero (node : Nat) :
    BitVec.ofNat 64 (node % 2) = (0 : Word) ↔ node % 2 = 0 := by
  constructor
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : node % 2 < 2^64),
      show (0 : Word).toNat = 0 by decide] at numeric
    exact numeric
  · intro equal
    rw [equal]
    rfl

theorem cap_advance_guard_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1) :
    (capAdvanceGuardState checking state).pc =
      if node % 2 = 0 then capNavigationPC checking .sibling
      else capNavigationPC checking .ascend := by
  have rootPC := cap_advance_root_pc checking state node pc index root bounded
  simp only [if_neg nonroot] at rootPC
  have rootIndex : (capAdvanceRootState checking state).getReg .x20 =
      BitVec.ofNat 64 node := (cap_flow_register _ _ _).trans index
  unfold capAdvanceGuardState capAdvanceParityFlow
  rw [cap_flow_equal_pc, cap_navigation_parity _ node rootIndex bounded,
    show (capNavigationState .parity (capAdvanceRootState checking state)).getReg .x0 =
      0 by rfl]
  simp only [parity_word_zero]
  rw [cap_navigation_pc, rootPC]
  cases checking <;> split <;> rfl

theorem cap_advance_guard_memory (checking : Bool) (state : MachineState) :
    (capAdvanceGuardState checking state).mem = state.mem := by
  simp only [capAdvanceGuardState, capAdvanceRootState, cap_flow_memory,
    cap_navigation_memory]

theorem cap_advance_guard_register (checking : Bool) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x7) :
    (capAdvanceGuardState checking state).getReg reg = state.getReg reg := by
  rw [capAdvanceGuardState, cap_flow_register]
  simp only [capNavigationState, capNavigationInstruction, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside),
    capAdvanceRootState, cap_flow_register]

theorem cap_advance_guard_execute (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry checking)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (3 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capAdvanceGuardState checking state) allowCoins
          return result.charge 3 0) := by
  have rootPC := cap_advance_root_pc checking state node pc index root bounded
  simp only [if_neg nonroot] at rootPC
  have parityFetch : fetch (capWalkImage checking)
      (capNavigationState .parity (capAdvanceRootState checking state)) =
        some (.base (capFlowInstruction (capAdvanceParityFlow checking))) := by
    cases checking
    · apply cap_image_fetch _ (capNavigationState .parity (capAdvanceRootState false state))
        102 _ (by decide)
      · rw [cap_navigation_pc, rootPC]
        rfl
      · rfl
    · apply cap_image_fetch _ (capNavigationState .parity (capAdvanceRootState true state))
        150 _ (by decide)
      · rw [cap_navigation_pc, rootPC]
        rfl
      · rfl
  rw [show 3 + fuel = 1 + (1 + (1 + fuel)) by omega,
    cap_advance_root_execute checking state pc,
    cap_navigation_image_execute checking .parity _ rootPC,
    cap_flow_execute _ _ _ parityFetch]
  simp only [bind_assoc, pure_bind, capAdvanceGuardState, charge_pair]

end CommitGolfCandidate
