import CommitGolfCandidate.CapKnownDecision

/-! Complete marked-node visit macros in both cap images. Finalized occupancy
drives the actual load/BEQ; known-node navigation then changes only the node
index and PC. No query is issued on either internal or known-leaf visits. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capVisitMarks (checking : Bool) : Reg := if checking then .x9 else .x22
def capMarkedPrepare (checking : Bool) (state : MachineState) : MachineState :=
  capVisitBranchState 20 (capVisitPrefix (capVisitMarks checking) state 3)
def capMarkedVisitState (checking : Bool) (state : MachineState) (node : Nat) : MachineState :=
  capKnownState checking (capMarkedPrepare checking state) node

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_marked_prepare_memory (checking : Bool) (state : MachineState) :
    (capMarkedPrepare checking state).mem = state.mem := by
  rw [capMarkedPrepare, cap_visit_branch_memory, cap_visit_prefix_memory _ _ 3 (by decide)]

theorem cap_marked_prepare_register (checking : Bool) (state : MachineState)
    (reg : Reg) (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23) :
    (capMarkedPrepare checking state).getReg reg = state.getReg reg := by
  rw [capMarkedPrepare, cap_visit_branch_register]
  exact cap_visit_prefix_register _ _ 3 (by decide) reg outside

theorem cap_marked_prepare_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit checking)
    (base : state.getReg (capVisitMarks checking) = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (present : marked node = true) :
    (capMarkedPrepare checking state).pc = capKnownEntry checking := by
  have selected : CapMarksRegister (capVisitMarks checking) := by
    cases checking <;> simp [capVisitMarks, CapMarksRegister]
  have mark := cap_visit_mark_ready _ state node marked selected base index positive bounded ready
  rw [present] at mark
  rw [capMarkedPrepare, cap_visit_branch_pc _ _ true mark,
    cap_visit_prefix_pc _ _ 3 (by decide), pc]
  cases checking <;> rfl

/-- The occupancy load and its known-node branch pay exactly four cycles. -/
theorem cap_marked_prepare_execute (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit checking)
    (base : state.getReg (capVisitMarks checking) = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (bounded : node < 256) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (4 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capMarkedPrepare checking state) allowCoins
          return result.charge 4 0) := by
  have selected : CapMarksRegister (capVisitMarks checking) := by
    cases checking <;> simp [capVisitMarks, CapMarksRegister]
  have fetched : CapVisitFetched (capWalkImage checking) (capVisitMarks checking)
      (capKnownVisit checking) := by
    cases checking
    · exact cap_open_visit_fetched
    · exact cap_check_visit_fetched
  have branchPC : (capVisitPrefix (capVisitMarks checking) state 3).pc =
      if checking then 4616 else 4432 := by
    rw [cap_visit_prefix_pc _ _ 3 (by decide), pc]
    cases checking <;> rfl
  have branch : fetch (capWalkImage checking) (capVisitPrefix (capVisitMarks checking) state 3) =
      some (.base (.BEQ .x6 .x0 20)) := by
    cases checking
    · exact cap_open_visit_branch_fetched _ branchPC
    · exact cap_check_visit_branch_fetched _ branchPC
  rw [show 4 + fuel = 3 + (1 + fuel) by omega,
    cap_visit_execute _ _ _ fetched state pc
      (cap_visit_load_valid _ state node selected base index bounded),
    cap_visit_branch_execute _ _ _ branch]
  simp only [bind_assoc, pure_bind, capMarkedPrepare, charge_pair]

theorem cap_marked_visit_execute (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit checking)
    (base : state.getReg (capVisitMarks checking) = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (leaves : state.getReg (capKnownLeafRegister checking) = 128)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (present : marked node = true) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) ((4 + (if node < 128 then 3 else 2)) + fuel)
        state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capMarkedVisitState checking state node) allowCoins
          return result.charge (4 + (if node < 128 then 3 else 2)) 0) := by
  have nextPC := cap_marked_prepare_pc checking state node pc base index positive bounded
    marked ready present
  have nextIndex : (capMarkedPrepare checking state).getReg .x20 = BitVec.ofNat 64 node :=
    (cap_marked_prepare_register checking state .x20 (by decide)).trans index
  have nextLeaves : (capMarkedPrepare checking state).getReg
      (capKnownLeafRegister checking) = 128 := by
    rw [cap_marked_prepare_register]
    · exact leaves
    · cases checking <;> decide
  rw [Nat.add_assoc, cap_marked_prepare_execute checking state node pc base index bounded,
    cap_known_decision_execute checking _ node nextPC nextIndex nextLeaves bounded]
  simp only [bind_assoc, pure_bind, capMarkedVisitState, charge_pair]

theorem cap_marked_visit_memory (checking : Bool) (state : MachineState) (node : Nat) :
    (capMarkedVisitState checking state node).mem = state.mem := by
  rw [capMarkedVisitState, cap_known_state_memory, cap_marked_prepare_memory]

theorem cap_marked_visit_node (checking : Bool) (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capMarkedVisitState checking state node).getReg .x20 =
      BitVec.ofNat 64 (if node < 128 then 2 * node else node) := by
  apply cap_known_state_node
  exact (cap_marked_prepare_register checking state .x20 (by decide)).trans index

end CommitGolfCandidate
