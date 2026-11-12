import CommitGolfCandidate.CapOpenRecordMarks
import CommitGolfCandidate.CapOpenPathSlots

/-! Exact lower sibling slots after the occupancy store. The path-copy theorem
uses its current entry as a fresh reference; separate local frames then recover
the original record-entry heap digest. A later bounded retained-input frame
connects that digest to the ABI trapdoor. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordGroupState capOpenRecordState
  capOpenRecordPathState capOpenSaltedState

theorem cap_open_record_group_output_read (state : MachineState) (position : Nat)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (marks : state.getReg .x22 = 28672)
    (address count : Nat) (high : 32768 ≤ address) (small : address+count ≤ 2^64) :
    readBuffer (capOpenRecordState state) address count =
      readBuffer (capOpenRecordGroupState state) address count := by
  have frame := cap_open_group_retained_inputs (address+count)
    (capOpenRecordGroupState state) (capOpenRecordGroupState state)
    (256+position/65536) small (by omega)
    ((cap_open_record_group_register state .x22 (by decide)).trans marks)
    (cap_open_record_group_index state position positionBound loaded leaves)
    (cap_open_retained_refl _ _)
  rw [capOpenRecordState]
  exact cap_open_retained_read (address+count) _ _ address count high (by omega) frame

theorem cap_open_record_sibling_slot (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (high : 32768 ≤ cursor)
    (rootAligned : rootBase % 8 = 0) (heapBelow : rootBase+1073741824 ≤ cursor)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) (marks : state.getReg .x22 = 28672)
    (ordinal : Nat) (ordinalBound : ordinal < 16) :
    readBuffer (capOpenRecordState state) (cursor+32+32*ordinal) 32 =
      readBuffer state
        (rootBase+32*(((16777216+position)/2^ordinal) ^^^ 1)) 32 := by
  have small : cursor+544 < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have ready := cap_open_record_path_ready rootBase limit cursor position state pc
    roots pointer aligned space positionBound loaded leaves
  have pathCursor : ((capOpenRecordPathState state).getReg .x25).toNat = cursor+32 := by
    rw [cap_open_record_path_cursor, pointer]
    change (BitVec.ofNat 64 cursor + BitVec.ofNat 64 32).toNat = _
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cursor+32 < 2^64)]
  have index := cap_open_record_path_index state position loaded leaves
  have slots := cap_open_path_loop_slots rootBase limit (cursor+32) 16
    (16777216+position) (capOpenRecordPathState state) (capOpenRecordPathState state)
    limitBound rootAligned (by omega) ready (by omega) index
    (by rw [pathCursor] <;> omega) (fun _ _ => rfl) ordinal ordinalBound
  rw [pathCursor, ← capOpenRecordGroupState] at slots
  have selfFrame := cap_open_path_loop_input_frame rootBase limit (cursor+32) 16
    (capOpenRecordPathState state) (capOpenRecordPathState state) limitBound ready
    (by rw [pathCursor] <;> omega) (fun _ _ => rfl)
  have quotient := Nat.div_le_self (16777216+position) (2^ordinal)
  have siblingBound : ((16777216+position)/2^ordinal) ^^^ 1 < 33554432 :=
    Nat.xor_lt_two_pow (n := 25) (by omega) (by decide)
  have sourceBelow : rootBase+32*(((16777216+position)/2^ordinal) ^^^ 1)+32 ≤ cursor := by
    omega
  have groupToPath := cap_open_frame_read (cursor+32) (capOpenRecordPathState state)
    (capCountedRun capOpenPathState 16 (capOpenRecordPathState state))
    (rootBase+32*(((16777216+position)/2^ordinal) ^^^ 1)) 32 (by omega) selfFrame
  rw [← capOpenRecordGroupState] at groupToPath
  have localFrame := cap_open_record_before_group_frame rootBase limit cursor position
    state pc roots pointer aligned space limitBound positionBound loaded leaves
  have groupToOriginal := cap_open_frame_read cursor state (capOpenRecordGroupState state)
    (rootBase+32*(((16777216+position)/2^ordinal) ^^^ 1)) 32 sourceBelow localFrame
  rw [cap_open_record_group_output_read state position positionBound loaded leaves marks
    _ 32 (by omega) (by omega), slots]
  exact groupToPath.symm.trans groupToOriginal

theorem cap_open_record_salt_slot (rootBase saltBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (salts : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (high : 32768 ≤ cursor)
    (saltAligned : saltBase % 8 = 0) (saltBelow : saltBase+32*position+32 ≤ cursor)
    (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) (marks : state.getReg .x22 = 28672) :
    readBuffer (capOpenRecordState state) cursor 32 =
      readBuffer state (saltBase+32*position) 32 := by
  have small : cursor+544 < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have source := cap_open_record_salt_address state position saltBase loaded salts
  have destination := (cap_open_record_prepare_register state 3 (by decide) .x25
    (by decide)).trans pointer
  have copied := cap_copy_digest false (capOpenRecordPrefix state 3)
    (saltBase+32*position) cursor source destination (by omega) aligned
    (by omega) (by omega) (Or.inl saltBelow)
  have salted : readBuffer (capOpenSaltedState state) cursor 32 =
      readBuffer state (saltBase+32*position) 32 := by
    rw [capOpenSaltedState]
    exact copied.trans (read_buffer_memory_congr _ _
      (cap_open_record_prepare_memory state 3 (by decide)) _ 32)
  have pathToSalted : readBuffer (capOpenRecordPathState state) cursor 32 =
      readBuffer (capOpenSaltedState state) cursor 32 := by
    rw [capOpenRecordPathState]
    exact read_buffer_memory_congr _ _ (cap_open_record_tail_memory _) cursor 32
  have ready := cap_open_record_path_ready rootBase limit cursor position state pc
    roots pointer aligned space positionBound loaded leaves
  have pathCursor : ((capOpenRecordPathState state).getReg .x25).toNat = cursor+32 := by
    rw [cap_open_record_path_cursor, pointer]
    change (BitVec.ofNat 64 cursor + BitVec.ofNat 64 32).toNat = _
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : cursor+32 < 2^64)]
  have selfFrame := cap_open_path_loop_input_frame rootBase limit (cursor+32) 16
    (capOpenRecordPathState state) (capOpenRecordPathState state) limitBound ready
    (by rw [pathCursor] <;> omega) (fun _ _ => rfl)
  have groupToPath := cap_open_frame_read (cursor+32) (capOpenRecordPathState state)
    (capCountedRun capOpenPathState 16 (capOpenRecordPathState state))
    cursor 32 (by omega) selfFrame
  rw [← capOpenRecordGroupState] at groupToPath
  rw [cap_open_record_group_output_read state position positionBound loaded leaves
    marks cursor 32 high (by omega), groupToPath, pathToSalted, salted]

end CommitGolfCandidate
