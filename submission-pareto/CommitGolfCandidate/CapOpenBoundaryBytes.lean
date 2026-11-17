import CommitGolfCandidate.CapOpenDfsRun
import CommitGolfCandidate.CapDfsSerialization

/-! Actual opening boundary copies emit the source heap digest and preserve
every byte below the output cursor. The input heap and serialized output must
remain separate; the natural bounds here state that condition explicitly. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

theorem cap_unknown_open_digest (state : MachineState) (node rootBase cursor : Nat)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootAligned : rootBase % 8 = 0) (cursorAligned : cursor % 8 = 0)
    (rootBound : rootBase + 32*node + 32 ≤ cursor)
    (cursorBound : cursor + 32 ≤ 2^64) :
    readBuffer (capUnknownOpenState state) cursor 32 =
      readBuffer state (rootBase + 32*node) 32 := by
  have preparedRoots := (cap_marked_prepare_register false state .x9 (by decide)).trans roots
  have preparedIndex := (cap_marked_prepare_register false state .x20 (by decide)).trans index
  have preparedPointer := (cap_marked_prepare_register false state .x25 (by decide)).trans pointer
  have copied := cap_boundary_digest false (capMarkedPrepare false state) node rootBase cursor
    preparedRoots preparedIndex preparedPointer
    (by simp only [capBoundarySource, Bool.false_eq_true, ↓reduceIte]; omega)
    cursorAligned (by
      simp only [capBoundarySource, Bool.false_eq_true, ↓reduceIte]
      omega)
    cursorBound (Or.inl rootBound)
  change readBuffer (capBoundaryState false (capMarkedPrepare false state)) cursor 32 = _
  simpa only [capBoundaryDestination, capBoundarySource, Bool.false_eq_true, ↓reduceIte,
    read_buffer_memory_congr _ _ (cap_marked_prepare_memory false state)] using copied

theorem cap_unknown_open_byte_before (state : MachineState)
    (node rootBase cursor address : Nat)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0)
    (cursorBound : cursor + 32 ≤ 2^64) (before : address < cursor) :
    (capUnknownOpenState state).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have copied := cap_boundary_byte_outside false (capMarkedPrepare false state)
    node rootBase cursor address
    ((cap_marked_prepare_register false state .x9 (by decide)).trans roots)
    ((cap_marked_prepare_register false state .x20 (by decide)).trans index)
    ((cap_marked_prepare_register false state .x25 (by decide)).trans pointer)
    aligned cursorBound (by omega) (Or.inl before)
  change (capBoundaryState false (capMarkedPrepare false state)).getByte
    (BitVec.ofNat 64 address) = _
  rw [copied]
  simp only [MachineState.getByte, MachineState.getMem, cap_marked_prepare_memory]

end CommitGolfCandidate
