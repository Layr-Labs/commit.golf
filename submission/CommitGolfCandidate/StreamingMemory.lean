import CommitGolfCandidate.Model
import CommitGolfCandidate.Memory
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.CheckEvaluation

/-! Memory refinement for destructive leaf streaming. Each compression reads the
current chain followed by one unread block before its reply replaces that block.
This module proves the reference memory transform; instruction execution is a
separate obligation. No assumption is made about the compression function. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The cursor addresses the chain, with the next message block immediately above
it. A reply consumes that block and becomes the next chain. -/
def streamingBlocks : MachineState → Nat → Nat → OracleComp World MachineState
  | state, _, 0 => pure state
  | state, cursor, count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
      streamingBlocks (writeBits state (BitVec.ofNat 64 (cursor + 32)) answer)
        (cursor + 32) count

/-- Streaming preserves any readable buffer wholly before or after its writes.
This covers salt storage, the digest heap, and the unread message suffix. -/
theorem streaming_blocks_read_outside (oracle : Oracle) (state : MachineState)
    (cursor count address bytes : Nat)
    (writeBound : cursor + 32 * (count + 1) ≤ 2^64)
    (readBound : address + bytes ≤ 2^64)
    (separate : address + bytes ≤ cursor + 32 ∨ cursor + 32 * (count + 1) ≤ address) :
    readBuffer (checkEvaluation oracle (streamingBlocks state cursor count)).1 address bytes =
      readBuffer state address bytes := by
  induction count generalizing state cursor with
  | zero => simp [streamingBlocks, check_evaluation_pure]
  | succ count ih =>
    rw [streamingBlocks, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (streamingBlocks
      (writeBits state (BitVec.ofNat 64 (cursor + 32))
        (oracle.compression (readBuffer state cursor 64))) (cursor + 32) count)).1
      address bytes = _
    rw [ih _ (cursor + 32) (by omega) (by rcases separate with h | h <;> omega)]
    exact write_bits_read_outside (bits := 256) state _ (cursor + 32) address bytes (by omega)
      readBound (by rcases separate with h | h <;> omega)

/-- The final chain equals the exact salted fold over the original unread blocks.
All later blocks are preserved after each reply write, so this includes arbitrary
compression outputs rather than only collision-free or sampled executions. -/
theorem streaming_blocks_digest (oracle : Oracle) (state : MachineState)
    (cursor count : Nat) (blocks : Nat → Digest)
    (aligned : cursor % 8 = 0)
    (bounded : cursor + 32 * (count + 1) ≤ 2^64)
    (data : ∀ i < count, readBuffer state (cursor + 32 + 32 * i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (streamingBlocks state cursor count)).1
        (cursor + 32 * count) 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i))
        (readBuffer state cursor 32) := by
  induction count generalizing state cursor blocks with
  | zero => simp [streamingBlocks, check_evaluation_pure]
  | succ count ih =>
    have input := read_compression_halves state cursor aligned
    rw [show cursor + 32 = cursor + 32 + 32 * 0 by omega, data 0 (by omega)] at input
    let answer := combine oracle.compression (readBuffer state cursor 32) (blocks 0)
    let next := writeBits state (BitVec.ofNat 64 (cursor + 32)) answer
    have nextData (i : Nat) (hi : i < count) :
        readBuffer next (cursor + 32 + 32 + 32 * i) 32 = blocks (i + 1) := by
      rw [show readBuffer next (cursor + 32 + 32 + 32 * i) 32 =
        readBuffer state (cursor + 32 + 32 + 32 * i) 32 from
          write_bits_read_outside (bits := 256) state answer (cursor + 32)
            (cursor + 32 + 32 + 32 * i) 32 (by omega) (by omega) (Or.inr (by omega))]
      rw [show cursor + 32 + 32 + 32 * i = cursor + 32 + 32 * (i + 1) by omega]
      exact data (i + 1) (by omega)
    have induction := ih next (cursor + 32) (fun i => blocks (i + 1))
      (by omega) (by omega) nextData
    rw [streamingBlocks, check_evaluation_public_bind]
    change readBuffer (checkEvaluation oracle (streamingBlocks
      (writeBits state (BitVec.ofNat 64 (cursor + 32))
        (oracle.compression (readBuffer state cursor 64))) (cursor + 32) count)).1
      (cursor + 32 * (count + 1)) 32 = _
    rw [input]
    change readBuffer (checkEvaluation oracle (streamingBlocks next (cursor + 32) count)).1
      (cursor + 32 * (count + 1)) 32 = _
    rw [show cursor + 32 * (count + 1) = cursor + 32 + 32 * count by omega, induction]
    have digest : readBuffer next (cursor + 32) 32 = answer := by
      have written := write_bits_digest state (cursor + 32) 0 answer (by decide) (by decide)
      simpa using written
    rw [digest]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, Nat.succ_eq_add_one]
    rfl

/-- Streaming makes precisely one public compression query for each block. -/
theorem streaming_blocks_queries (oracle : Oracle) (state : MachineState)
    (cursor count : Nat) :
    (checkEvaluation oracle (streamingBlocks state cursor count)).2 = count := by
  induction count generalizing state cursor with
  | zero => simp [streamingBlocks, check_evaluation_pure]
  | succ count ih =>
    rw [streamingBlocks, check_evaluation_public_bind]
    change 1 + (checkEvaluation oracle (streamingBlocks _ (cursor + 32) count)).2 = count + 1
    rw [ih]
    omega

end CommitGolfCandidate
