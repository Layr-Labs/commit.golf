import CommitGolfCandidate.CapOpenRecordLowFrame
import CommitGolfCandidate.CapMarkPointUpdate

/-! Exact occupancy effect of a complete opening record. The only changed
mark is its lower-path group leaf. Duplicate group records repeat a store of
one, while every other previously established mark remains unchanged. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState capOpenRecordGroupState

private theorem mark_word_aligned (node : Nat) : (28672+8*node) % 8 = 0 := by
  omega

private theorem mark_word_below (node cursor : Nat)
    (nodeBound : node < 512) (high : 32800 ≤ cursor) :
    28672+8*node+32 ≤ cursor := by
  omega

private theorem group_bound (position : Nat) (bounded : position < 16777216) :
    256+position/65536 < 512 := by omega

theorem cap_open_record_mark {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (one : state.getReg .x31 = 1) (node : Nat) (nodeBound : node < 512) :
    (capOpenRecordState state).getMem (capMarkAddress node) =
      if node = 256+position/65536 then 1 else state.getMem (capMarkAddress node) := by
  have groupMarks : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide) entry).trans entry.marks
  have groupIndex := cap_open_record_group_index entry
  have groupOne : (capOpenRecordGroupState state).getReg .x31 = 1 :=
    (cap_open_record_group_register state .x31 (by decide) entry).trans one
  have memory : (capOpenRecordState state).mem =
      ((capOpenRecordGroupState state).setMem
        (capMarkAddress (256+position/65536)) 1).mem := by
    rw [capOpenRecordState]
    simpa only [capMarkAddress, groupOne] using
      cap_open_group_memory (capOpenRecordGroupState state)
        (256+position/65536) groupMarks groupIndex
  have before := cap_open_record_before_group_word entry
    (28672+8*node) (mark_word_aligned node)
    (mark_word_below node cursor nodeBound entry.high)
  exact cap_mark_point_update state (capOpenRecordGroupState state)
    (capOpenRecordState state) (256+position/65536) node
    (group_bound position entry.positionBound) nodeBound memory
    (cap_mark_lookup_address state (capOpenRecordGroupState state) node before)

end CommitGolfCandidate
