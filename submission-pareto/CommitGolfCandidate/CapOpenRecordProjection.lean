import CommitGolfCandidate.CapOpenRecordStep

/-! Outer-loop handoff of the complete record macro. Only the explicitly
changed work registers are excluded from the register frame. Natural request
and index bounds decide the branch; the cursor advances by the record's 576
bytes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenRecordGroupState capOpenRecordState

theorem cap_open_record_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x30 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28 ∧
      reg ≠ .x24 ∧ reg ≠ .x27)
    {rootBase saltBase cursor limit position : Nat}
    (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordState state).getReg reg = state.getReg reg := by
  obtain ⟨h1, h6, h7, h23, h30, h25, h20, h28, h24, h27⟩ := outside
  rw [capOpenRecordState]
  exact (cap_open_group_register _ reg ⟨h7, h23, h24, h27⟩).trans
    (cap_open_record_group_register state reg ⟨h1, h6, h7, h23, h30, h25, h20, h28⟩ entry)

theorem cap_open_record_cursor {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordState state).getReg .x25 = BitVec.ofNat 64 (cursor + 576) := by
  rw [capOpenRecordState, cap_open_group_register _ .x25 (by decide),
    capOpenRecordGroupState, cap_open_path_loop_cursor,
    (cap_open_record_path_facts entry).2.2.1, ← BitVec.ofNat_add]

theorem cap_open_record_index_pointer {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    (capOpenRecordState state).getReg .x24 = state.getReg .x24 + 8 := by
  rw [capOpenRecordState, (cap_open_group_projection _).1,
    cap_open_record_group_register state .x24 (by decide) entry]

theorem cap_open_record_counter {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (remaining : Nat) (positive : 0 < remaining)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenRecordState state).getReg .x27 = BitVec.ofNat 64 (remaining-1) := by
  rw [capOpenRecordState]
  apply cap_open_group_counter _ remaining positive
  exact (cap_open_record_group_register state .x27 (by decide) entry).trans counter

theorem cap_open_record_exit {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (remaining : Nat) (positive : 0 < remaining) (remainingBound : remaining < 2^64)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenRecordState state).pc = if remaining = 1 then 4364 else 4212 := by
  have ready := cap_open_record_path_ready entry
  rw [capOpenRecordState]
  apply cap_open_group_exit _ remaining
  · rw [capOpenRecordGroupState]
    exact (cap_open_path_loop_finished rootBase limit entry.limitBound 14 _ ready).1
  · exact positive
  · exact remainingBound
  · exact (cap_open_record_group_register state .x27 (by decide) entry).trans counter

end CommitGolfCandidate
