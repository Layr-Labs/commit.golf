import CommitGolfCandidate.StreamingMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def heapStreamingBlocks (state : MachineState) (cursor count destination : Nat) :
    OracleComp World MachineState :=
  match count with
  | 0 => pure state
  | count + 1 => do
      let body ← streamingBlocks state cursor count
      let answer ← World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))
      return writeBits body (BitVec.ofNat 64 destination) answer

theorem heap_streaming_evaluation (oracle : Oracle) (state : MachineState)
    (cursor count destination : Nat) :
    (checkEvaluation oracle (heapStreamingBlocks state cursor (count + 1) destination)).1 =
      writeBits (checkEvaluation oracle (streamingBlocks state cursor count)).1
        (BitVec.ofNat 64 destination)
        (oracle.compression (readBuffer
          (checkEvaluation oracle (streamingBlocks state cursor count)).1
          (cursor + 32 * count) 64)) := by
  rw [heapStreamingBlocks, check_evaluation_bind]
  cases evaluated : checkEvaluation oracle (streamingBlocks state cursor count) with
  | mk body queries =>
    simp only [check_evaluation_public_bind, check_evaluation_pure]
    rfl

theorem heap_streaming_queries (oracle : Oracle) (state : MachineState)
    (cursor count destination : Nat) :
    (checkEvaluation oracle (heapStreamingBlocks state cursor count destination)).2 = count := by
  cases count with
  | zero => simp [heapStreamingBlocks, check_evaluation_pure]
  | succ count =>
    rw [heapStreamingBlocks, check_evaluation_bind]
    simp only [check_evaluation_public_bind, check_evaluation_pure,
      streaming_blocks_queries, Nat.add_zero, Nat.add_comm]

theorem heap_streaming_read_outside (oracle : Oracle) (state : MachineState)
    (cursor count destination address bytes : Nat)
    (writeBound : cursor + 32 * (count + 1) ≤ 2^64)
    (destinationBound : destination + 32 ≤ 2^64)
    (readBound : address + bytes ≤ 2^64)
    (prefixSeparate : address + bytes ≤ cursor + 32 ∨
      cursor + 32 * (count + 1) ≤ address)
    (heapSeparate : address + bytes ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer
      (checkEvaluation oracle (heapStreamingBlocks state cursor (count + 1) destination)).1
      address bytes = readBuffer state address bytes := by
  rw [heap_streaming_evaluation]
  exact (write_bits_read_outside (bits := 256) _ _ destination address bytes
    (by simpa using destinationBound) readBound (by simpa using heapSeparate)).trans
      (streaming_blocks_read_outside oracle state cursor count address bytes
        writeBound readBound prefixSeparate)

theorem heap_streaming_digest (oracle : Oracle) (state : MachineState)
    (cursor count destination : Nat) (blocks : Nat → Digest)
    (aligned : cursor % 8 = 0)
    (bounded : cursor + 32 * (count + 2) ≤ 2^64)
    (data : ∀ i < count + 1,
      readBuffer state (cursor + 32 + 32 * i) 32 = blocks i) :
    readBuffer
      (checkEvaluation oracle (heapStreamingBlocks state cursor (count + 1) destination)).1
      destination 32 =
      (List.range (count + 1)).foldl
        (fun digest i => combine oracle.compression digest (blocks i))
        (readBuffer state cursor 32) := by
  let body := (checkEvaluation oracle (streamingBlocks state cursor count)).1
  have chain : readBuffer body (cursor + 32 * count) 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i))
        (readBuffer state cursor 32) :=
    streaming_blocks_digest oracle state cursor count blocks aligned (by omega)
      (fun i hi => data i (by omega))
  have lastBlock : readBuffer body (cursor + 32 * count + 32) 32 = blocks count := by
    rw [show readBuffer body (cursor + 32 * count + 32) 32 =
      readBuffer state (cursor + 32 * count + 32) 32 from
        streaming_blocks_read_outside oracle state cursor count
          (cursor + 32 * count + 32) 32 (by omega) (by omega)
          (Or.inr (by omega))]
    rw [show cursor + 32 * count + 32 = cursor + 32 + 32 * count by omega]
    exact data count (by omega)
  have input : readBuffer body (cursor + 32 * count) 64 =
      (blocks count).append
        ((List.range count).foldl
          (fun digest i => combine oracle.compression digest (blocks i))
          (readBuffer state cursor 32)) := by
    rw [read_compression_halves body (cursor + 32 * count) (by omega), chain, lastBlock]
    rfl
  rw [heap_streaming_evaluation]
  let answer : BitVec 256 := oracle.compression (readBuffer body (cursor + 32 * count) 64)
  have written : readBuffer (writeBits body (BitVec.ofNat 64 destination)
      answer) destination 32 = answer := by
    simpa using write_bits_digest body destination 0 answer (by decide) (by decide)
  change readBuffer (writeBits body (BitVec.ofNat 64 destination)
      answer) destination 32 = _
  rw [written]
  change oracle.compression (readBuffer body (cursor + 32 * count) 64) = _
  rw [input, List.range_succ, List.foldl_append]
  rfl

end CommitGolfCandidate
