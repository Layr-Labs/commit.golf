import CommitGolfCandidate.CapOpenRecordProjection

/-! The complete record preserves the admitted high input interval below the
initial proof-output floor. The path uses a fresh self-reference, because
earlier records may already have changed occupancy words. No global equality
to the initial loader is asserted for those intentionally modified words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenSaltedState capOpenRecordPathState
  capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_retained_inputs (floor rootBase limit cursor position : Nat)
    (state reference : MachineState)
    (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (before : floor ≤ cursor)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (marks : state.getReg .x22 = 28672)
    (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference (capOpenRecordState state) := by
  have small : cursor+544 < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have prepared := cap_open_retained_memory floor state (capOpenRecordPrefix state 3)
    reference (cap_open_record_prepare_memory state 3 (by decide)) frame
  have copyPointer : (capOpenRecordPrefix state 3).getReg .x25 =
      BitVec.ofNat 64 cursor :=
    (cap_open_record_prepare_register state 3 (by decide) .x25 (by decide)).trans pointer
  have salted : CapOpenRetainedInputs floor reference (capOpenSaltedState state) := by
    rw [capOpenSaltedState]
    exact cap_open_retained_copy floor cursor _ reference copyPointer aligned
      (by omega) before prepared
  have pathFrame : CapOpenRetainedInputs floor reference
      (capOpenRecordPathState state) := by
    rw [capOpenRecordPathState]
    exact cap_open_retained_memory floor _ _ reference
      (cap_open_record_tail_memory _) salted
  have ready := cap_open_record_path_ready rootBase limit cursor position state
    pc roots pointer aligned space positionBound loaded leaves
  have pathCursor : (capOpenRecordPathState state).getReg .x25 =
      BitVec.ofNat 64 (cursor+32) := by
    rw [cap_open_record_path_cursor, pointer]
    exact (BitVec.ofNat_add cursor 32).symm
  have floorBound : floor ≤ ((capOpenRecordPathState state).getReg .x25).toNat := by
    rw [pathCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+32 < 2^64)]
    omega
  have loopSelf := cap_open_path_loop_input_frame rootBase limit floor 16
    (capOpenRecordPathState state) (capOpenRecordPathState state) limitBound ready
    floorBound (fun _ _ => rfl)
  have groupFrame : CapOpenRetainedInputs floor reference
      (capOpenRecordGroupState state) := by
    intro address high below
    rw [capOpenRecordGroupState]
    exact (loopSelf address below).trans (pathFrame address high below)
  rw [capOpenRecordState]
  exact cap_open_group_retained_inputs floor _ reference (256+position/65536)
    (by omega) (by omega)
    ((cap_open_record_group_register state .x22 (by decide)).trans marks)
    (cap_open_record_group_index state position positionBound loaded leaves) groupFrame

end CommitGolfCandidate
