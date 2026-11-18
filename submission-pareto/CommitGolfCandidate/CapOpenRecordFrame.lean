import CommitGolfCandidate.CapOpenRecordProjection
import CommitGolfCandidate.CapNonceFrame

/-! The complete record preserves the admitted high input interval below the
initial proof-output floor. The path uses a fresh self-reference, because
earlier records may already have changed occupancy words. No global equality
to the initial loader is asserted for those intentionally modified words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenSaltedState capOpenRecordPathState
  capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_retained_inputs (floor : Nat)
    {rootBase saltBase cursor limit position : Nat} {state : MachineState}
    (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (reference : MachineState) (before : floor ≤ cursor)
    (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference (capOpenRecordState state) := by
  have small := cap_open_record_at_small entry
  have aligned := entry.cursorAligned
  have prepared := cap_open_retained_memory floor state (capOpenRecordPrefix state 3)
    reference (cap_open_record_prepare_memory state 3 (by decide)) frame
  have copyPointer : (capOpenRecordPrefix state 3).getReg .x25 =
      BitVec.ofNat 64 cursor :=
    (cap_open_record_prepare_register state 3 (by decide) .x25 (by decide)).trans entry.pointer
  have salted : CapOpenRetainedInputs floor reference (capOpenSaltedState state) := by
    rw [capOpenSaltedState]
    exact cap_open_retained_nonce floor cursor _ reference copyPointer aligned
      (by omega) before prepared
  have facts := cap_open_record_path_facts entry
  have pathFrame : CapOpenRetainedInputs floor reference
      (capOpenRecordPathState state) := by
    intro address high below
    rw [cap_open_byte_of_word (capOpenSaltedState state) (capOpenRecordPathState state) address
      (by omega) (facts.2.2.2.2.2.2 _ (by omega) (by omega))]
    exact salted address high below
  have ready := cap_open_record_path_ready entry
  have floorBound : floor ≤ ((capOpenRecordPathState state).getReg .x25).toNat := by
    rw [facts.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+128 < 2^64)]
    omega
  have loopSelf := cap_open_path_loop_input_frame rootBase limit floor 14
    (capOpenRecordPathState state) (capOpenRecordPathState state) entry.limitBound ready
    floorBound (fun _ _ => rfl)
  have groupFrame : CapOpenRetainedInputs floor reference
      (capOpenRecordGroupState state) := by
    intro address high below
    rw [capOpenRecordGroupState]
    exact (loopSelf address below).trans (pathFrame address high below)
  rw [capOpenRecordState]
  exact cap_open_group_retained_inputs floor _ reference (256+position/65536)
    (by omega) (by have := entry.positionBound; omega)
    ((cap_open_record_group_register state .x22 (by decide) entry).trans entry.marks)
    (cap_open_record_group_index entry) groupFrame

end CommitGolfCandidate
