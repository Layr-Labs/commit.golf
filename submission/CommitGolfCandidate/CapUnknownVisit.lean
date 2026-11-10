import CommitGolfCandidate.CapMarkedVisit
import CommitGolfCandidate.CapBoundaryMemory
import CommitGolfCandidate.CapBoundaryGuard

/-! Actual unknown-node visits. Opening appends one heap digest. Checking tests
the full next digest before copying it into the reserved root heap. A short
proof pays only its occupancy read and guard, then reaches rejection without
performing any proof load or oracle query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capUnknownOpenState (state : MachineState) : MachineState :=
  capBoundaryState false (capMarkedPrepare false state)
def capUnknownCheckGuard (state : MachineState) : MachineState :=
  capBoundaryGuardState (capMarkedPrepare true state)
def capUnknownCheckState (state : MachineState) : MachineState :=
  capBoundaryState true (capUnknownCheckGuard state)

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_unknown_prepare_pc (checking : Bool) (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit checking)
    (base : state.getReg (capVisitMarks checking) = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (absent : marked node = false) :
    (capMarkedPrepare checking state).pc = if checking then 4636 else 4452 := by
  have selected : CapMarksRegister (capVisitMarks checking) := by
    cases checking <;> simp [capVisitMarks, CapMarksRegister]
  have mark := cap_visit_mark_ready _ state node marked selected base index positive bounded ready
  rw [absent] at mark
  rw [capMarkedPrepare, cap_visit_branch_pc _ _ false mark,
    cap_visit_prefix_pc _ _ 3 (by decide), pc]
  cases checking <;> rfl

theorem cap_unknown_open_execute (state : MachineState) (node rootBase cursor : Nat)
    (pc : state.pc = capKnownVisit false)
    (marks : state.getReg .x22 = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (absent : marked node = false)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (rootBound : rootBase + 32 * node + 32 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (cursorBound : cursor + 32 ≤ MEMORY_BYTES) (aligned : cursor % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage false) (15 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage false) fuel
            (capUnknownOpenState state) allowCoins
          return result.charge 15 0) := by
  have nextPC := cap_unknown_prepare_pc false state node pc marks index positive bounded
    marked ready absent
  have nextIndex := (cap_marked_prepare_register false state .x20 (by decide)).trans index
  have nextRoots := (cap_marked_prepare_register false state .x9 (by decide)).trans roots
  have nextProof := (cap_marked_prepare_register false state .x25 (by decide)).trans proof
  rw [show 15 + fuel = 4 + (11 + fuel) by omega,
    cap_marked_prepare_execute false state node pc marks index bounded,
    cap_boundary_copy_execute false _ node rootBase cursor nextPC nextRoots nextIndex
      rootBound rootAligned nextProof cursorBound aligned]
  simp only [bind_assoc, pure_bind, charge_pair, capUnknownOpenState]

theorem cap_unknown_check_guard_pc (state : MachineState) (node cursor limit : Nat)
    (pc : state.pc = capKnownVisit true)
    (marks : state.getReg .x9 = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (absent : marked node = false)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (noWrap : cursor + 32 < 2^64) (limitBound : limit < 2^64) :
    (capUnknownCheckGuard state).pc =
      if cursor + 32 ≤ limit then capBoundaryEntry true else 4808 := by
  apply cap_boundary_guard_pc _ cursor limit
    (cap_unknown_prepare_pc true state node pc marks index positive bounded marked ready absent)
  · exact (cap_marked_prepare_register true state .x25 (by decide)).trans proof
  · exact (cap_marked_prepare_register true state .x22 (by decide)).trans proofEnd
  · exact noWrap
  · exact limitBound

theorem cap_unknown_check_guard_execute (state : MachineState) (node : Nat)
    (pc : state.pc = capKnownVisit true)
    (marks : state.getReg .x9 = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (absent : marked node = false) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (6 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage true) fuel
            (capUnknownCheckGuard state) allowCoins
          return result.charge 6 0) := by
  have nextPC := cap_unknown_prepare_pc true state node pc marks index positive bounded
    marked ready absent
  rw [show 6 + fuel = 4 + (2 + fuel) by omega,
    cap_marked_prepare_execute true state node pc marks index bounded,
    cap_boundary_guard_execute _ nextPC]
  simp only [bind_assoc, pure_bind, charge_pair, capUnknownCheckGuard]

/-- An admitted full boundary digest costs seventeen ordinary instructions. -/
theorem cap_unknown_check_execute (state : MachineState) (node cursor limit : Nat)
    (pc : state.pc = capKnownVisit true)
    (marks : state.getReg .x9 = 20480)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 256)
    (marked : Nat → Bool) (ready : CapMarksReady state 128 0 marked)
    (absent : marked node = false) (roots : state.getReg .x18 = 12288)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (limitBound : limit ≤ MEMORY_BYTES) (enough : cursor + 32 ≤ limit)
    (aligned : cursor % 8 = 0) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (17 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage true) fuel
            (capUnknownCheckState state) allowCoins
          return result.charge 17 0) := by
  have small : limit < 2^64 := by simp only [MEMORY_BYTES] at limitBound; omega
  have nextPC := cap_unknown_check_guard_pc state node cursor limit pc marks index positive
    bounded marked ready absent proof proofEnd (by omega) small
  rw [if_pos enough] at nextPC
  have frame : ∀ reg, reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 →
      (capUnknownCheckGuard state).getReg reg = state.getReg reg := by
    intro reg outside
    rw [capUnknownCheckGuard, cap_boundary_guard_register _ reg outside.1]
    exact cap_marked_prepare_register true state reg outside
  rw [show 17 + fuel = 6 + (11 + fuel) by omega,
    cap_unknown_check_guard_execute state node pc marks index positive bounded marked ready absent,
    cap_check_boundary_copy_execute _ node cursor nextPC
      ((frame .x18 (by decide)).trans roots)
      ((frame .x20 (by decide)).trans index) bounded
      ((frame .x25 (by decide)).trans proof) (by omega) aligned]
  simp only [bind_assoc, pure_bind, charge_pair, capUnknownCheckState]

end CommitGolfCandidate
