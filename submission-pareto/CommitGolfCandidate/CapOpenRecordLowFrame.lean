import CommitGolfCandidate.CapOpenRecordFrame
import CommitGolfCandidate.CapOpenReadDigest

/-! Before its single occupancy store, a record only writes at its growing
high output cursor. All earlier bytes, including previous occupancy words,
are preserved. A record also leaves the fourth word of its salt field and
every word after its 576 bytes unchanged. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenSaltedState capOpenRecordPathState
  capOpenRecordGroupState

private theorem byte_memory (state next : MachineState) (same : next.mem = state.mem)
    (address : Nat) :
    next.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address) := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem cap_open_record_before_group_frame {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state) :
    CapOpenInputFrame cursor state (capOpenRecordGroupState state) := by
  have small := cap_open_record_at_small entry
  have aligned := entry.cursorAligned
  have preparedPointer : (capOpenRecordPrefix state 3).getReg .x25 =
      BitVec.ofNat 64 cursor :=
    (cap_open_record_prepare_register state 3 (by decide) .x25 (by decide)).trans entry.pointer
  have saltedFrame : CapOpenInputFrame cursor state (capOpenSaltedState state) := by
    intro address below
    rw [capOpenSaltedState]
    exact (cap_nonce_byte_outside (capOpenRecordPrefix state 3) cursor address
      preparedPointer aligned (by omega) (by omega) (Or.inl below)).trans
      (byte_memory state _ (cap_open_record_prepare_memory state 3 (by decide)) address)
  have facts := cap_open_record_path_facts entry
  have pathFrame : CapOpenInputFrame cursor state (capOpenRecordPathState state) := by
    intro address below
    rw [cap_open_byte_of_word (capOpenSaltedState state) (capOpenRecordPathState state) address
      (by omega) (facts.2.2.2.2.2.2 _ (by omega) (by omega))]
    exact saltedFrame address below
  have ready := cap_open_record_path_ready entry
  have floor : cursor ≤ ((capOpenRecordPathState state).getReg .x25).toNat := by
    rw [facts.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+128 < 2^64)]
    omega
  rw [capOpenRecordGroupState]
  exact cap_open_path_loop_input_frame rootBase limit cursor 14 _ state
    entry.limitBound ready floor pathFrame

theorem cap_open_record_before_group_word {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address : Nat) (wordAligned : address % 8 = 0) (inside : address+32 ≤ cursor) :
    (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have frame := cap_open_record_before_group_frame entry
  have same := cap_open_frame_read cursor state (capOpenRecordGroupState state)
    address 32 inside frame
  have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) same
  simpa only [read_digest_word _ _ 0 wordAligned (by decide),
    Nat.mul_zero, Nat.add_zero] using word

/-- Bytes below the path's output, from the path entry to the group state. -/
theorem cap_open_record_group_low_read {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address count : Nat) (inside : address + count ≤ cursor + 128) :
    readBuffer (capOpenRecordGroupState state) address count =
      readBuffer (capOpenRecordPathState state) address count := by
  have small := cap_open_record_at_small entry
  have facts := cap_open_record_path_facts entry
  have ready := cap_open_record_path_ready entry
  have floor : cursor + 128 ≤ ((capOpenRecordPathState state).getReg .x25).toNat := by
    rw [facts.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+128 < 2^64)]
  have frame := cap_open_path_loop_input_frame rootBase limit (cursor+128) 14
    (capOpenRecordPathState state) (capOpenRecordPathState state) entry.limitBound ready
    floor (fun _ _ => rfl)
  rw [capOpenRecordGroupState]
  exact cap_open_frame_read (cursor+128) _ _ address count inside frame

/-- Words after the record's 576 bytes, from the path entry to the group state. -/
theorem cap_open_record_group_ahead_word {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address : Nat) (aligned : address % 8 = 0) (bounded : address + 32 ≤ 2^64)
    (after : cursor + 576 ≤ address) :
    (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) =
      (capOpenRecordPathState state).getMem (BitVec.ofNat 64 address) := by
  have small := cap_open_record_at_small entry
  have facts := cap_open_record_path_facts entry
  have ready := cap_open_record_path_ready entry
  have start : ((capOpenRecordPathState state).getReg .x25).toNat = cursor + 128 := by
    rw [facts.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+128 < 2^64)]
  have frame := cap_open_path_loop_ahead_frame rootBase limit (cursor+576) 14
    (capOpenRecordPathState state) (capOpenRecordPathState state) entry.limitBound ready
    (by have := start; omega) (fun _ _ _ => rfl)
  apply cap_open_word_of_bytes _ _ address aligned
  intro i hi
  rw [capOpenRecordGroupState]
  exact frame (address+i) (by omega) (by omega)

/-- The record leaves the fourth word of its salt field and every word after its 576 bytes. -/
theorem cap_open_record_high_word {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address : Nat) (aligned : address % 8 = 0) (bounded : address + 32 ≤ 2^64)
    (which : address = cursor + 24 ∨ cursor + 576 ≤ address) :
    (capOpenRecordState state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have small := cap_open_record_at_small entry
  have high := entry.high
  have positionBound := entry.positionBound
  have facts := cap_open_record_path_facts entry
  have marks : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide) entry).trans entry.marks
  have addressSmall : address < 2^64 := by omega
  have markSmall : 28672+8*(256+position/65536) < 2^64 := by omega
  have markOther : address ≠ 28672+8*(256+position/65536) := by omega
  have different : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (28672+8*(256+position/65536)) :=
    cap_stub_word_ne _ _ addressSmall markSmall markOther
  have memory := cap_open_group_memory (capOpenRecordGroupState state) (256+position/65536) marks
    (cap_open_record_group_index entry)
  have viaStore : (capOpenRecordState state).getMem (BitVec.ofNat 64 address) =
      ((capOpenRecordGroupState state).setMem (BitVec.ofNat 64 (28672+8*(256+position/65536)))
        ((capOpenRecordGroupState state).getReg .x31)).getMem (BitVec.ofNat 64 address) := by
    rw [capOpenRecordState]
    exact cap_open_get_mem_of_mem memory _
  have stored : (capOpenRecordState state).getMem (BitVec.ofNat 64 address) =
      (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) := by
    rw [viaStore, cap_open_set_mem_get, if_neg different]
  have grouped : (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) =
      (capOpenRecordPathState state).getMem (BitVec.ofNat 64 address) := by
    rcases which with equal | after
    · have inside : address + 32 ≤ cursor + 128 := by omega
      have low := cap_open_record_group_low_read entry address 32 inside
      have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) low
      simpa only [read_digest_word _ _ 0 aligned (by decide), Nat.mul_zero, Nat.add_zero] using word
    · exact cap_open_record_group_ahead_word entry address aligned bounded after
  have outsideTail : address < cursor + 32 ∨ cursor + 128 ≤ address := by omega
  have pathToSalted := facts.2.2.2.2.2.2 address addressSmall outsideTail
  have outsideSalt : ∀ word : Fin 3, BitVec.ofNat 64 address ≠
      (capOpenRecordPrefix state 3).getReg .x25 + BitVec.ofNat 64 (8*word.val) := by
    intro word equal
    have wordBound := word.isLt
    have wordSmall : cursor + 8 * word.val < 2^64 := by omega
    have wordOther : address ≠ cursor + 8 * word.val := by omega
    rw [cap_open_record_prepare_register state 3 (by decide) .x25 (by decide), entry.pointer,
      ← BitVec.ofNat_add] at equal
    exact cap_stub_word_ne _ _ addressSmall wordSmall wordOther equal
  have saltedToState : (capOpenSaltedState state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
    rw [capOpenSaltedState, cap_nonce_eight_memory_outside _ _ outsideSalt]
    exact congrFun (cap_open_record_prepare_memory state 3 (by decide)) _
  exact stored.trans (grouped.trans (pathToSalted.trans saltedToState))

end CommitGolfCandidate
