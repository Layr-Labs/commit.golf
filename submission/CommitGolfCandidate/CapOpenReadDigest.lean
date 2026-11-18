import CommitGolfCandidate.CapOpenRunFrame

/-! Digest reads through the opening's byte frame. The fixed floor may include
the completed record prefix or an already emitted cap block. No whole-memory
equality is assumed for the growing output buffer. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_frame_read (floor : Nat) (reference state : MachineState)
    (address count : Nat) (inside : address + count ≤ floor)
    (frame : CapOpenInputFrame floor reference state) :
    readBuffer state address count = readBuffer reference address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro offset member
  have small : offset < count := Finset.mem_range.mp member
  rw [frame (address+offset) (by omega)]

theorem cap_unknown_open_reference_digest (state reference : MachineState)
    (node rootBase cursor floor : Nat)
    (roots : state.getReg .x9 = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (rootAligned : rootBase % 8 = 0) (cursorAligned : cursor % 8 = 0)
    (sourceBelow : rootBase + 32*node + 32 ≤ floor) (floorBefore : floor ≤ cursor)
    (cursorBound : cursor + 32 ≤ 2^64)
    (frame : CapOpenInputFrame floor reference state) :
    readBuffer (capUnknownOpenState state) cursor 32 =
      readBuffer reference (rootBase + 32*node) 32 := by
  rw [cap_unknown_open_digest state node rootBase cursor roots index pointer rootAligned
    cursorAligned (by omega) cursorBound]
  exact cap_open_frame_read floor reference state _ 32 sourceBelow frame

/-- Every future supported traversal preserves an already emitted digest when
its end is below the tracked output floor. -/
theorem cap_open_future_digest (marked : Nat → Bool)
    (rootBase limit floor : Nat) (reference : MachineState)
    (limitBound : limit ≤ MEMORY_BYTES) (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (count : Nat) (control : CapDfsControl) (state final : MachineState)
    (ready : CapOpenReadReady marked rootBase limit floor reference control state)
    (reached : final ∈ support (capDfsRun false marked count control state))
    (address : Nat) (inside : address + 32 ≤ floor) :
    readBuffer final address 32 = readBuffer reference address 32 := by
  have finished := cap_open_run_input_frame marked rootBase limit floor reference
    limitBound rootBound rootAligned count control state final ready reached
  exact cap_open_frame_read floor reference final address 32 inside finished.inputFrame

theorem cap_open_abi_heap_before_prefix (positions : Positions) :
    capProgram.layout.trapdoor + 16384 ≤
      capProgram.layout.proof + 576 * positions.card := by
  norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
    LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
  omega

end CommitGolfCandidate
