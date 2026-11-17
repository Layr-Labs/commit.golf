import CommitGolfCandidate.CapOpenPathLoop
import CommitGolfCandidate.CapOpenInputFrame

/-! Frames and index/cursor effects of the counted lower-path loop. Copies write
only at the growing output cursor. Bytes below the initial output floor, and
registers not used by the loop, remain unchanged. These statements do not
identify the copied siblings with an honest tree until a heap frame is supplied. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenPathState capOpenPathCopied

private theorem byte_memory (state next : MachineState) (same : next.mem = state.mem)
    (address : Nat) :
    next.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address) := by
  simp only [MachineState.getByte, MachineState.getMem, same]

theorem cap_open_path_byte_before (state : MachineState) (cursor address : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (bounded : cursor+32 ≤ 2^64)
    (before : address < cursor) :
    (capOpenPathState state).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have prepared := (cap_open_path_prepare_register state 3 (by decide) .x25
    (by decide)).trans pointer
  have copied := cap_copy_byte_outside false (capOpenPathPrefix state 3) cursor address
    prepared aligned bounded (by omega) (Or.inl before)
  have tailMemory : (capOpenPathState state).mem = (capOpenPathCopied state).mem := by
    rw [capOpenPathState]
    exact cap_open_path_tail_memory _
  have copiedByte : (capOpenPathCopied state).getByte (BitVec.ofNat 64 address) =
      (capOpenPathPrefix state 3).getByte (BitVec.ofNat 64 address) := by
    simpa only [capOpenPathCopied] using copied
  exact (byte_memory _ _ tailMemory address).trans
    (copiedByte.trans (byte_memory _ _ (cap_open_path_prepare_memory state 3 (by decide))
      address))

theorem cap_open_path_loop_register (remaining : Nat) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28) :
    (capCountedRun capOpenPathState remaining state).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
      rw [capCountedRun.eq_2, ih]
      exact cap_open_path_register state reg outside

theorem cap_open_path_loop_index (remaining : Nat) (state : MachineState) (node : Nat)
    (bounded : node < 2^64) (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capCountedRun capOpenPathState remaining state).getReg .x20 =
      BitVec.ofNat 64 (node / 2^remaining) := by
  induction remaining generalizing state node with
  | zero => simpa only [capCountedRun.eq_1, Nat.pow_zero, Nat.div_one] using index
  | succ remaining ih =>
      rw [capCountedRun.eq_2, ih (capOpenPathState state) (node/2) (by omega)
        (cap_open_path_index state node bounded index)]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem cap_open_path_loop_input_frame (rootBase limit floor remaining : Nat)
    (state reference : MachineState) (limitBound : limit ≤ MEMORY_BYTES)
    (ready : CapOpenPathReady rootBase limit remaining state)
    (floorBound : floor ≤ (state.getReg .x25).toNat)
    (frame : CapOpenInputFrame floor reference state) :
    CapOpenInputFrame floor reference (capCountedRun capOpenPathState remaining state) := by
  induction remaining generalizing state with
  | zero => exact frame
  | succ remaining ih =>
      obtain ⟨cursor, pointer, aligned, space⟩ := ready.cursor
      have small : cursor+32 < 2^64 := by
        simp only [MEMORY_BYTES] at limitBound
        omega
      have cursorNat : (state.getReg .x25).toNat = cursor := by
        rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have nextFloor : floor ≤ ((capOpenPathState state).getReg .x25).toNat := by
        rw [(cap_open_path_projection state).1, pointer]
        change floor ≤ (BitVec.ofNat 64 cursor + BitVec.ofNat 64 32).toNat
        rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
        rw [cursorNat] at floorBound
        omega
      rw [capCountedRun.eq_2]
      apply ih (capOpenPathState state)
        (cap_open_path_ready_next rootBase limit remaining state limitBound ready) nextFloor
      intro address before
      rw [cap_open_path_byte_before state cursor address pointer aligned (by omega)
        (by rw [cursorNat] at floorBound; omega)]
      exact frame address before

end CommitGolfCandidate
