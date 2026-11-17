import CommitGolfCandidate.CapOpenRecordStep

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28 ∧
      reg ≠ .x24 ∧ reg ≠ .x27) :
    (capOpenRecordState state).getReg reg = state.getReg reg := by
  rw [capOpenRecordState]
  exact (cap_open_group_register _ reg
    ⟨outside.2.1, outside.2.2.1, outside.2.2.2.2.2.2.1,
      outside.2.2.2.2.2.2.2⟩).trans
    (cap_open_record_group_register state reg
      ⟨outside.1, outside.2.1, outside.2.2.1, outside.2.2.2.1,
        outside.2.2.2.2.1, outside.2.2.2.2.2.1⟩)

theorem cap_open_record_cursor (state : MachineState) :
    (capOpenRecordState state).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 544 := by
  rw [capOpenRecordState, cap_open_group_register _ .x25 (by decide),
    capOpenRecordGroupState, cap_open_path_loop_cursor,
    cap_open_record_path_cursor]
  change state.getReg .x25 + BitVec.ofNat 64 32 + BitVec.ofNat 64 (32*16) =
    state.getReg .x25 + BitVec.ofNat 64 544
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem cap_open_record_index_pointer (state : MachineState) :
    (capOpenRecordState state).getReg .x24 = state.getReg .x24 + 8 := by
  rw [capOpenRecordState, (cap_open_group_projection _).1,
    cap_open_record_group_register state .x24 (by decide)]

theorem cap_open_record_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenRecordState state).getReg .x27 = BitVec.ofNat 64 (remaining-1) := by
  rw [capOpenRecordState]
  apply cap_open_group_counter _ remaining positive
  exact (cap_open_record_group_register state .x27 (by decide)).trans counter

theorem cap_open_record_exit (state : MachineState)
    (rootBase limit cursor position remaining : Nat)
    (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (positive : 0 < remaining) (remainingBound : remaining < 2^64)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenRecordState state).pc = if remaining = 1 then 4364 else 4212 := by
  have ready := cap_open_record_path_ready rootBase limit cursor position state
    pc roots pointer aligned space positionBound loaded leaves
  rw [capOpenRecordState]
  apply cap_open_group_exit _ remaining
  · rw [capOpenRecordGroupState]
    exact (cap_open_path_loop_finished rootBase limit limitBound 16 _ ready).1
  · exact positive
  · exact remainingBound
  · exact (cap_open_record_group_register state .x27 (by decide)).trans counter

end CommitGolfCandidate
