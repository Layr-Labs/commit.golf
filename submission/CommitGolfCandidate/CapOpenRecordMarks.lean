import CommitGolfCandidate.CapOpenRecordLowFrame
import CommitGolfCandidate.CapMarkPointUpdate

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

theorem cap_open_record_mark (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (high : 32800 ≤ cursor)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (marks : state.getReg .x22 = 28672) (one : state.getReg .x31 = 1)
    (node : Nat) (nodeBound : node < 512) :
    (capOpenRecordState state).getMem (capMarkAddress node) =
      if node = 256+position/65536 then 1 else state.getMem (capMarkAddress node) := by
  have groupMarks : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide)).trans marks
  have groupIndex := cap_open_record_group_index state position positionBound loaded leaves
  have groupOne : (capOpenRecordGroupState state).getReg .x31 = 1 :=
    (cap_open_record_group_register state .x31 (by decide)).trans one
  have memory : (capOpenRecordState state).mem =
      ((capOpenRecordGroupState state).setMem
        (capMarkAddress (256+position/65536)) 1).mem := by
    rw [capOpenRecordState]
    simpa only [capMarkAddress, groupOne] using
      cap_open_group_memory (capOpenRecordGroupState state)
        (256+position/65536) groupMarks groupIndex
  have before := cap_open_record_before_group_word rootBase limit cursor position state pc
    roots pointer aligned space limitBound positionBound loaded leaves
    (28672+8*node) (mark_word_aligned node)
    (mark_word_below node cursor nodeBound high)
  exact cap_mark_point_update state (capOpenRecordGroupState state)
    (capOpenRecordState state) (256+position/65536) node (group_bound position positionBound) nodeBound memory
    (cap_mark_lookup_address state (capOpenRecordGroupState state) node before)

end CommitGolfCandidate
