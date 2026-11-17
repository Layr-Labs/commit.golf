import CommitGolfCandidate.StreamingLeaf

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem streaming_commit_leaf_digest (oracle : Oracle) (state : MachineState)
    (address count destination : Nat) (blocks : Nat → Digest)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (above : 32 ≤ address)
    (bounded : address + 32 * (count + 1) < 2^64)
    (heapBound : destination + 32 ≤ 2^64)
    (data : ∀ i < count + 1, readBuffer state (address + 32 * i) 32 = blocks i) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state (count + 1))).1
      destination 32 =
      (List.range (count + 1)).foldl
        (fun digest i => combine oracle.compression digest (blocks i))
        (readBuffer state (address - 32) 32) := by
  have pointerNat : (state.getReg .x8).toNat = address := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heapNat : (state.getReg .x23).toNat = destination := by
    rw [heapPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [read_buffer_memory_congr _ _ (commit_leaf_loop_memory oracle state (count + 1)),
    pointerNat, heapNat]
  apply heap_streaming_digest oracle state (address - 32) count destination blocks
    (by omega) (by omega)
  intro i hi
  rw [show address - 32 + 32 + 32 * i = address + 32 * i by omega]
  exact data i hi

theorem streaming_commit_leaf_read_outside (oracle : Oracle) (state : MachineState)
    (source count destination address bytes : Nat)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (above : 32 ≤ source) (writeBound : source + 32 * (count + 1) < 2^64)
    (heapBound : destination + 32 ≤ 2^64) (readBound : address + bytes ≤ 2^64)
    (separate : address + bytes ≤ source ∨ source + 32 * (count + 1) ≤ address)
    (heapSeparate : address + bytes ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state (count + 1))).1 address bytes =
      readBuffer state address bytes := by
  have pointerNat : (state.getReg .x8).toNat = source := by
    rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have heapNat : (state.getReg .x23).toNat = destination := by
    rw [heapPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [read_buffer_memory_congr _ _ (commit_leaf_loop_memory oracle state (count + 1)),
    pointerNat, heapNat]
  apply heap_streaming_read_outside oracle state (source - 32) count destination address bytes
    (by omega) heapBound readBound _ heapSeparate
  rcases separate with before | after <;> omega

theorem streaming_commit_leaf_hash (oracle : Oracle) (state : MachineState)
    (address destination : Nat) (salt : Digest) (value : Entry)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 address)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (above : 32 ≤ address)
    (bounded : address + 256 < 2^64) (heapBound : destination + 32 ≤ 2^64)
    (initial : readBuffer state (address - 32) 32 = salt)
    (data : ∀ i < 8, readBuffer state (address + 32 * i) 32 =
      value.extractLsb' (256 * i) 256) :
    readBuffer (checkEvaluation oracle (commitLeafLoop state 8)).1 destination 32 =
      leafDigest oracle.compression salt value := by
  rw [streaming_commit_leaf_digest oracle state address 7 destination _ pointer heapPointer
    aligned above bounded heapBound data, initial]
  rfl

end CommitGolfCandidate
