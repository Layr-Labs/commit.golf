import CommitGolfCandidate.CapCheckDfsFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] readBuffer capUnknownCheckGuard capUnknownCheckState capBoundaryState

private theorem read_bytes_congr (left right : MachineState) (address count : Nat)
    (bytes : ∀ offset<count,
      left.getByte (BitVec.ofNat 64 (address+offset))=
        right.getByte (BitVec.ofNat 64 (address+offset))) :
    readBuffer left address count=readBuffer right address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset member
  rw [bytes offset (Finset.mem_range.mp member)]

theorem cap_unknown_check_digest (state : MachineState) (node cursor : Nat)
    (roots : state.getReg .x18=12288)
    (index : state.getReg .x20=BitVec.ofNat 64 node)
    (pointer : state.getReg .x25=BitVec.ofNat 64 cursor)
    (bounded : node<512) (above : 32768≤cursor)
    (aligned : cursor%8=0) (cursorBound : cursor+32≤2^64) :
    capReadRoot (capUnknownCheckState state) node = readBuffer state cursor 32 := by
  have base : (capUnknownCheckGuard state).getReg .x18=BitVec.ofNat 64 12288 := by
    exact (cap_unknown_check_guard_register state .x18 (by decide)).trans roots
  have copied := cap_boundary_digest true (capUnknownCheckGuard state) node 12288 cursor
    base ((cap_unknown_check_guard_register state .x20 (by decide)).trans index)
    ((cap_unknown_check_guard_register state .x25 (by decide)).trans pointer)
    aligned (by simp only [capBoundaryDestination,↓reduceIte]; omega)
    cursorBound (by simp only [capBoundaryDestination,↓reduceIte]; omega)
    (Or.inr (by simp only [capBoundaryDestination,capBoundarySource,↓reduceIte]; omega))
  unfold capReadRoot capUnknownCheckState
  change readBuffer (capBoundaryState true (capUnknownCheckGuard state))
    (12288+32*node) 32 = _
  simpa only [capBoundaryDestination,capBoundarySource,↓reduceIte,
    read_buffer_memory_congr _ _ (cap_unknown_check_guard_memory state)] using copied

theorem cap_unknown_check_other_root (state : MachineState) (node other cursor : Nat)
    (roots : state.getReg .x18=12288)
    (index : state.getReg .x20=BitVec.ofNat 64 node)
    (pointer : state.getReg .x25=BitVec.ofNat 64 cursor)
    (bounded : node<512) (otherBound : other<512) (distinct : other≠node) :
    capReadRoot (capUnknownCheckState state) other = capReadRoot state other := by
  have base : (capUnknownCheckGuard state).getReg .x18=BitVec.ofNat 64 12288 :=
    (cap_unknown_check_guard_register state .x18 (by decide)).trans roots
  unfold capReadRoot
  apply read_bytes_congr
  intro offset small
  have frame := cap_boundary_byte_outside true (capUnknownCheckGuard state) node 12288
    cursor (12288+32*other+offset) base
    ((cap_unknown_check_guard_register state .x20 (by decide)).trans index)
    ((cap_unknown_check_guard_register state .x25 (by decide)).trans pointer)
    (by simp only [capBoundaryDestination,↓reduceIte]; omega)
    (by simp only [capBoundaryDestination,↓reduceIte]; omega) (by omega)
    (by simp only [capBoundaryDestination,↓reduceIte]; omega)
  rw [capUnknownCheckState,frame]
  simp only [MachineState.getByte,MachineState.getMem,cap_unknown_check_guard_memory]

theorem cap_unknown_check_root_map (state : MachineState) (node other cursor : Nat)
    (roots : state.getReg .x18=12288)
    (index : state.getReg .x20=BitVec.ofNat 64 node)
    (pointer : state.getReg .x25=BitVec.ofNat 64 cursor)
    (bounded : node<512) (otherBound : other<512)
    (above : 32768≤cursor) (aligned : cursor%8=0) (cursorBound : cursor+32≤2^64) :
    capReadRoot (capUnknownCheckState state) other =
      if other=node then readBuffer state cursor 32 else capReadRoot state other := by
  by_cases same : other=node
  · subst other
    rw [if_pos rfl]
    exact cap_unknown_check_digest state node cursor roots index pointer bounded
      above aligned cursorBound
  · rw [if_neg same]
    exact cap_unknown_check_other_root state node other cursor roots index pointer
      bounded otherBound same

end CommitGolfCandidate
