import CommitGolfCandidate.CapOpenPathFrame
import CommitGolfCandidate.CapOpenReadDigest

/-! Exact sibling slots emitted by the actual lower-path loop. Each copied
digest is read through the original heap-byte frame; the rest of the loop
preserves that newly emitted block below its advanced output floor. The tree
interpretation of the heap slots is deliberately a later handoff. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenPathState

theorem cap_open_path_cursor_nat (rootBase limit remaining : Nat) (state : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES)
    (ready : CapOpenPathReady rootBase limit (remaining+1) state) :
    ((capOpenPathState state).getReg .x25).toNat =
      (state.getReg .x25).toNat + 32 := by
  obtain ⟨cursor, pointer, aligned, space⟩ := ready.cursor
  have small : cursor+32 < 2^64 := by
    simp only [MEMORY_BYTES] at limitBound
    omega
  rw [(cap_open_path_projection state).1, pointer]
  change (BitVec.ofNat 64 cursor + BitVec.ofNat 64 32).toNat =
    (BitVec.ofNat 64 cursor).toNat + 32
  rw [← BitVec.ofNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (by omega : cursor < 2^64)]

theorem cap_open_path_loop_slots (rootBase limit floor count node : Nat)
    (state reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES) (rootAligned : rootBase % 8 = 0)
    (heapBelow : rootBase + 1073741824 ≤ floor)
    (ready : CapOpenPathReady rootBase limit count state)
    (nodeBound : node < 33554432)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (before : floor ≤ (state.getReg .x25).toNat)
    (frame : CapOpenInputFrame floor reference state)
    (ordinal : Nat) (inside : ordinal < count) :
    readBuffer (capCountedRun capOpenPathState count state)
        ((state.getReg .x25).toNat + 32*ordinal) 32 =
      readBuffer reference (rootBase + 32*((node / 2^ordinal) ^^^ 1)) 32 := by
  induction count generalizing state node ordinal with
  | zero => omega
  | succ count ih =>
      obtain ⟨cursor, pointer, aligned, space⟩ := ready.cursor
      have small : cursor+32 < 2^64 := by
        simp only [MEMORY_BYTES] at limitBound
        omega
      have current : (state.getReg .x25).toNat = cursor := by
        rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have sibling : node ^^^ 1 < 33554432 :=
        Nat.xor_lt_two_pow (n := 25) nodeBound (by decide)
      have nextReady := cap_open_path_ready_next rootBase limit count state limitBound ready
      have nextCursor := cap_open_path_cursor_nat rootBase limit count state limitBound ready
      have nextBefore : floor ≤ ((capOpenPathState state).getReg .x25).toNat := by omega
      have nextFrame : CapOpenInputFrame floor reference (capOpenPathState state) := by
        intro address low
        rw [cap_open_path_byte_before state cursor address pointer aligned (by omega)
          (by rw [current] at before; omega)]
        exact frame address low
      rw [capCountedRun.eq_2]
      cases ordinal with
      | zero =>
          have emitted := cap_open_path_digest state node rootBase cursor index ready.roots
            pointer rootAligned aligned (by rw [current] at before; omega) (by omega)
          have original := cap_open_frame_read floor reference state
            (rootBase + 32*(node ^^^ 1)) 32 (by omega) frame
          have preserved := cap_open_path_loop_input_frame rootBase limit
            ((capOpenPathState state).getReg .x25).toNat count (capOpenPathState state)
            (capOpenPathState state) limitBound nextReady (Nat.le_refl _)
            (by intro address low; rfl)
          have readSame := cap_open_frame_read
            ((capOpenPathState state).getReg .x25).toNat (capOpenPathState state)
            (capCountedRun capOpenPathState count (capOpenPathState state))
            cursor 32 (by rw [nextCursor, current]) preserved
          simpa only [current, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]
            using readSame.trans (emitted.trans original)
      | succ ordinal =>
          have result := ih (node/2) (capOpenPathState state) nextReady (by omega)
            (cap_open_path_index state node (by omega) index) nextBefore nextFrame ordinal
            (by omega)
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at result
          rw [nextCursor] at result
          have address : (state.getReg .x25).toNat + 32 + 32*ordinal =
              (state.getReg .x25).toNat + 32*(ordinal+1) := by omega
          simpa only [address] using result

end CommitGolfCandidate
