import CommitGolfCandidate.StreamingLeaf

/-! Leaf digest and locality consequences of the instruction bridge. The checker
still uses its scratch buffer; commitment streams through consumed message data.
Both compute the same salted compression fold. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The reference cursor starts one digest below the message. A complete streamed
leaf leaves its result in the final consumed block, rather than fixed scratch. -/
theorem streaming_commit_leaf_digest (oracle : Oracle) (state : MachineState)
    (address count : Nat) (blocks : Nat → Digest)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 32 ≤ address)
    (bounded : address + 32 * count < 2^64)
    (data : ∀ i < count, readBuffer state (address + 32 * i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state count)).1
      (address - 32 + 32 * count) 32 =
      (List.range count).foldl
        (fun digest i => combine oracle.compression digest (blocks i))
        (readBuffer state (address - 32) 32) := by
  have pointerNat : (state.getReg .x8).toNat = address := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [read_buffer_memory_congr _ _ (commit_leaf_loop_memory oracle state count), pointerNat]
  apply streaming_blocks_digest oracle state (address - 32) count blocks (by omega) (by omega)
  intro i hi
  rw [show address - 32 + 32 + 32 * i = address + 32 * i by omega]
  exact data i hi

/-- The machine leaf preserves salt/heap buffers and unread message suffixes.
This statement deliberately excludes consumed input blocks. -/
theorem streaming_commit_leaf_read_outside (oracle : Oracle) (state : MachineState)
    (source count address bytes : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (above : 32 ≤ source) (writeBound : source + 32 * count < 2^64)
    (readBound : address + bytes ≤ 2^64)
    (separate : address + bytes ≤ source ∨ source + 32 * count ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state count)).1 address bytes =
      readBuffer state address bytes := by
  have pointerNat : (state.getReg .x8).toNat = source := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [read_buffer_memory_congr _ _ (commit_leaf_loop_memory oracle state count), pointerNat]
  apply streaming_blocks_read_outside oracle state (source - 32) count address bytes
    (by omega) readBound
  rcases separate with before | after <;> omega

/-- The final streamed digest is exactly the existing security model's salted
eight-block leaf hash. This does not change the compression oracle or its domain. -/
theorem streaming_commit_leaf_hash (oracle : Oracle) (state : MachineState)
    (address : Nat) (salt : Digest) (value : Entry)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (aligned : address % 8 = 0) (above : 32 ≤ address)
    (bounded : address + 256 < 2^64)
    (initial : readBuffer state (address - 32) 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32 * i) 32 =
      value.extractLsb' (256 * i) 256) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state 8)).1 (address + 224) 32 =
      leafDigest oracle.compression salt value := by
  rw [show address + 224 = address - 32 + 32 * 8 by omega,
    streaming_commit_leaf_digest oracle state address 8 _ pointer aligned above bounded data,
    initial]
  rfl

end CommitGolfCandidate
