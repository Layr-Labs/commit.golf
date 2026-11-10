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

private theorem mark_word_aligned (node : Nat) : (20480+8*node) % 8 = 0 := by
  omega

private theorem mark_word_below (node cursor : Nat)
    (nodeBound : node < 256) (high : 22560 ≤ cursor) :
    20480+8*node+32 ≤ cursor := by
  omega

private theorem group_bound (position : Nat) (bounded : position < 16777216) :
    128+position/131072 < 256 := by omega

theorem cap_open_record_mark (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+576 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (high : 22560 ≤ cursor)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (marks : state.getReg .x22 = 20480) (one : state.getReg .x31 = 1)
    (node : Nat) (nodeBound : node < 256) :
    (capOpenRecordState state).getMem (capMarkAddress node) =
      if node = 128+position/131072 then 1 else state.getMem (capMarkAddress node) := by
  have groupMarks : (capOpenRecordGroupState state).getReg .x22 = 20480 :=
    (cap_open_record_group_register state .x22 (by decide)).trans marks
  have groupIndex := cap_open_record_group_index state position positionBound loaded leaves
  have groupOne : (capOpenRecordGroupState state).getReg .x31 = 1 :=
    (cap_open_record_group_register state .x31 (by decide)).trans one
  have memory : (capOpenRecordState state).mem =
      ((capOpenRecordGroupState state).setMem
        (capMarkAddress (128+position/131072)) 1).mem := by
    rw [capOpenRecordState]
    simpa only [capMarkAddress, groupOne] using
      cap_open_group_memory (capOpenRecordGroupState state)
        (128+position/131072) groupMarks groupIndex
  have before := cap_open_record_before_group_word rootBase limit cursor position state pc
    roots pointer aligned space limitBound positionBound loaded leaves
    (20480+8*node) (mark_word_aligned node)
    (mark_word_below node cursor nodeBound high)
  exact cap_mark_point_update state (capOpenRecordGroupState state)
    (capOpenRecordState state) (128+position/131072) node (group_bound position positionBound) nodeBound memory
    (cap_mark_lookup_address state (capOpenRecordGroupState state) node before)

end CommitGolfCandidate
