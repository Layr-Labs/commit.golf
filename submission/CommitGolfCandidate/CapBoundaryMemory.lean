import CommitGolfCandidate.CapBoundaryCopy

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capBoundaryPrefix capDigestCopyPrefix

def capBoundarySource (checking : Bool) (node rootBase cursor : Nat) : Nat :=
  if checking then cursor else rootBase + 32 * node
def capBoundaryDestination (checking : Bool) (node rootBase cursor : Nat) : Nat :=
  if checking then rootBase + 32 * node else cursor

theorem cap_boundary_state_memory (checking : Bool) (state : MachineState) :
    (capBoundaryState checking state).mem =
      (capDigestCopyPrefix checking (capBoundaryPrefix checking state 2) 8).mem := rfl

theorem cap_boundary_pointers (checking : Bool) (state : MachineState)
    (node rootBase cursor : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor) :
    (capBoundaryPrefix checking state 2).getReg (capCopySource checking) =
      BitVec.ofNat 64 (capBoundarySource checking node rootBase cursor) ∧
    (capBoundaryPrefix checking state 2).getReg (capCopyDestination checking) =
      BitVec.ofNat 64 (capBoundaryDestination checking node rootBase cursor) := by
  have root := cap_boundary_address checking state node rootBase base index
  have pointer := (cap_boundary_prefix_register checking state 2 (by decide)
    .x25 (by decide)).trans proof
  cases checking <;>
    simp only [capCopySource, capCopyDestination, capBoundarySource,
      capBoundaryDestination, Bool.false_eq_true, ↓reduceIte, root, pointer,
      and_self]

theorem cap_boundary_digest (checking : Bool) (state : MachineState)
    (node rootBase cursor : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (sourceAligned : capBoundarySource checking node rootBase cursor % 8 = 0)
    (destinationAligned : capBoundaryDestination checking node rootBase cursor % 8 = 0)
    (sourceBound : capBoundarySource checking node rootBase cursor + 32 ≤ 2^64)
    (destinationBound : capBoundaryDestination checking node rootBase cursor + 32 ≤ 2^64)
    (separate :
      capBoundarySource checking node rootBase cursor + 32 ≤
        capBoundaryDestination checking node rootBase cursor ∨
      capBoundaryDestination checking node rootBase cursor + 32 ≤
        capBoundarySource checking node rootBase cursor) :
    readBuffer (capBoundaryState checking state)
        (capBoundaryDestination checking node rootBase cursor) 32 =
      readBuffer state (capBoundarySource checking node rootBase cursor) 32 := by
  have pointers := cap_boundary_pointers checking state node rootBase cursor base index proof
  rw [read_buffer_memory_congr _ _ (cap_boundary_state_memory checking state)]
  rw [cap_copy_digest checking _ _ _ pointers.1 pointers.2 sourceAligned
    destinationAligned sourceBound destinationBound separate]
  exact read_buffer_memory_congr _ _ (cap_boundary_prefix_memory checking state 2 (by decide))
    (capBoundarySource checking node rootBase cursor) 32

theorem cap_boundary_byte_outside (checking : Bool) (state : MachineState)
    (node rootBase cursor address : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : capBoundaryDestination checking node rootBase cursor % 8 = 0)
    (destinationBound : capBoundaryDestination checking node rootBase cursor + 32 ≤ 2^64)
    (addressBound : address < 2^64)
    (outside : address < capBoundaryDestination checking node rootBase cursor ∨
      capBoundaryDestination checking node rootBase cursor + 32 ≤ address) :
    (capBoundaryState checking state).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have pointers := cap_boundary_pointers checking state node rootBase cursor base index proof
  change (capDigestCopyPrefix checking (capBoundaryPrefix checking state 2) 8).getByte
    (BitVec.ofNat 64 address) = _
  rw [cap_copy_byte_outside checking _ _ address pointers.2 aligned destinationBound
    addressBound outside]
  have frame := cap_boundary_prefix_memory checking state 2 (by decide)
  simp only [MachineState.getByte, MachineState.getMem, frame]

theorem cap_boundary_marks_ready (checking : Bool) (state : MachineState)
    (node rootBase cursor : Nat) (marked : Nat → Bool)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (destinationBound : capBoundaryDestination checking node rootBase cursor + 32 ≤ 2^64)
    (separate : capBoundaryDestination checking node rootBase cursor + 32 ≤ 28672 ∨
      32768 ≤ capBoundaryDestination checking node rootBase cursor)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capBoundaryState checking state) 256 0 marked := by
  have pointers := cap_boundary_pointers checking state node rootBase cursor base index proof
  apply cap_marks_ready_memory _ _ 256 0 marked
    (cap_boundary_state_memory checking state)
  apply cap_copy_marks_ready checking _ _ marked pointers.2 destinationBound separate
  exact cap_marks_ready_memory state (capBoundaryPrefix checking state 2) 256 0 marked
    (cap_boundary_prefix_memory checking state 2 (by decide)) ready

theorem cap_boundary_high_bytes (checking : Bool) (state reference : MachineState)
    (node rootBase cursor : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : capBoundaryDestination checking node rootBase cursor % 8 = 0)
    (low : capBoundaryDestination checking node rootBase cursor + 32 ≤ 32768)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capBoundaryState checking state) reference := by
  have pointers := cap_boundary_pointers checking state node rootBase cursor base index proof
  apply cap_high_bytes_memory _ _ reference (cap_boundary_state_memory checking state)
  apply cap_copy_high_bytes checking _ reference _ pointers.2 aligned low
  exact cap_high_bytes_memory state (capBoundaryPrefix checking state 2) reference
    (cap_boundary_prefix_memory checking state 2 (by decide)) frame

end CommitGolfCandidate
