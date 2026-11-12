import CommitGolfCandidate.CapOpenRecordsFrame

/-! Before its single occupancy store, a record only writes at its growing
high output cursor. All earlier bytes, including previous occupancy words,
are preserved. This is a local frame to the current record entry, not a claim
that earlier record marks equal the original loader's zero workspace. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenSaltedState capOpenRecordPathState
  capOpenRecordGroupState

private theorem byte_memory (state next : MachineState) (same : next.mem = state.mem)
    (address : Nat) :
    next.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address) := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem cap_open_record_before_group_frame (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216) :
    CapOpenInputFrame cursor state (capOpenRecordGroupState state) := by
  have small : cursor+544 < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  have preparedPointer : (capOpenRecordPrefix state 3).getReg .x25 =
      BitVec.ofNat 64 cursor :=
    (cap_open_record_prepare_register state 3 (by decide) .x25 (by decide)).trans pointer
  have saltedFrame : CapOpenInputFrame cursor state (capOpenSaltedState state) := by
    intro address below
    rw [capOpenSaltedState]
    exact (cap_copy_byte_outside false (capOpenRecordPrefix state 3) cursor address
      preparedPointer aligned (by omega) (by omega) (Or.inl below)).trans
      (byte_memory state _ (cap_open_record_prepare_memory state 3 (by decide)) address)
  have pathFrame : CapOpenInputFrame cursor state (capOpenRecordPathState state) := by
    intro address below
    rw [capOpenRecordPathState]
    exact (byte_memory _ _ (cap_open_record_tail_memory _) address).trans
      (saltedFrame address below)
  have ready := cap_open_record_path_ready rootBase limit cursor position state
    pc roots pointer aligned space positionBound loaded leaves
  have pathCursor : (capOpenRecordPathState state).getReg .x25 =
      BitVec.ofNat 64 (cursor+32) := by
    rw [cap_open_record_path_cursor, pointer]
    exact (BitVec.ofNat_add cursor 32).symm
  have floor : cursor ≤ ((capOpenRecordPathState state).getReg .x25).toNat := by
    rw [pathCursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+32 < 2^64)]
    omega
  rw [capOpenRecordGroupState]
  exact cap_open_path_loop_input_frame rootBase limit cursor 16 _ state
    limitBound ready floor pathFrame

theorem cap_open_record_before_group_word (rootBase limit cursor position : Nat)
    (state : MachineState) (pc : state.pc = 4212)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (space : cursor+544 ≤ limit)
    (limitBound : limit ≤ MEMORY_BYTES) (positionBound : position < 16777216)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (leaves : state.getReg .x19 = 16777216)
    (address : Nat) (wordAligned : address % 8 = 0) (inside : address+32 ≤ cursor) :
    (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have frame := cap_open_record_before_group_frame rootBase limit cursor position state
    pc roots pointer aligned space limitBound positionBound loaded leaves
  have same := cap_open_frame_read cursor state (capOpenRecordGroupState state)
    address 32 inside frame
  have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) same
  simpa only [read_digest_word _ _ 0 wordAligned (by decide),
    Nat.mul_zero, Nat.add_zero] using word

end CommitGolfCandidate
