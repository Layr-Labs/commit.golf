import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.HeapModel

/-! Contents of the authentication path emitted by the submitted opening image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem path_prepared_source (state : MachineState) :
    (openingPathPreparedState state).getReg .x23 =
      state.getReg .x9 + ((state.getReg .x20 ^^^ 1) <<< 5) := by rfl

private theorem path_prepared_output (state : MachineState) :
    (openingPathPreparedState state).getReg .x25 = state.getReg .x25 := by rfl

private theorem path_prepared_memory (state : MachineState) :
    (openingPathPreparedState state).mem = state.mem := by rfl

private theorem path_copied_memory (state : MachineState) :
    (openingPathState state).mem = (openingCopyState (openingPathPreparedState state)).mem := rfl

/-- One actual path iteration writes the digest at its computed sibling address. -/
theorem opening_path_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x9 + ((state.getReg .x20 ^^^ 1) <<< 5) = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (openingPathState state) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (path_copied_memory state)]
  rw [opening_copy_digest _ source destination
    ((path_prepared_source state).trans sourcePointer)
    ((path_prepared_output state).trans destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate]
  exact read_buffer_memory_congr _ _ (path_prepared_memory state) _ _

/-- The path iteration changes no digest disjoint from its output slot. -/
theorem opening_path_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (openingPathState state) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (path_copied_memory state)]
  rw [opening_copy_preserves_digest _ destination address
    ((path_prepared_output state).trans destinationPointer)
    aligned destinationBound readBound separate]
  exact read_buffer_memory_congr _ _ (path_prepared_memory state) _ _

private theorem sibling_pointer (base node : Nat) :
    BitVec.ofNat 64 base + ((BitVec.ofNat 64 node ^^^ 1) <<< 5) =
      BitVec.ofNat 64 (base+32*(node ^^^ 1)) := by
  change BitVec.ofNat 64 base + ((BitVec.ofNat 64 node ^^^ BitVec.ofNat 64 1) <<< 5) = _
  rw [← BitVec.ofNat_xor, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 base + (BitVec.ofNat 64 (node ^^^ 1) * BitVec.ofNat 64 32) = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm (node ^^^ 1)]

/-- Every sibling record emitted by the whole path loop is read from the original
heap. Later copies preserve earlier proof records and the source heap. -/
theorem opening_path_records (state : MachineState) (heap : Nat → Digest)
    (base node destination count : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (nodePointer : state.getReg .x20 = BitVec.ofNat 64 node)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (heapAligned : base % 8 = 0) (destinationAligned : destination % 8 = 0)
    (nodeBound : node < 2^25) (separated : base+2^30 ≤ destination)
    (bounded : destination+32*count ≤ MEMORY_BYTES)
    (data : ∀ slot < 2^25, readBuffer state (base+32*slot) 32 = heap slot) :
    ∀ level < count,
      readBuffer (openingPathState^[count] state) (destination+32*level) 32 =
        heap ((node / 2^level) ^^^ 1) := by
  induction count generalizing state node destination with
  | zero => intro level inside; omega
  | succ count ih =>
    have bound64 : destination+32*(count+1) < 2^64 := by
      simp only [MEMORY_BYTES] at bounded
      omega
    have siblingBound : node ^^^ 1 < 2^25 := Nat.xor_lt_two_pow nodeBound (by decide)
    let next := openingPathState state
    have nextDestination : next.getReg .x25 = BitVec.ofNat 64 (destination+32) := by
      rw [(opening_path_registers state).1, destinationPointer]
      exact (BitVec.ofNat_add (n := 64) destination 32).symm
    have nextDestinationNat : (next.getReg .x25).toNat = destination+32 := by
      rw [nextDestination, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have nextHeap : next.getReg .x9 = BitVec.ofNat 64 base :=
      (opening_path_registers state).2.2.2.2.trans heapPointer
    have nextNode : next.getReg .x20 = BitVec.ofNat 64 (node/2) := by
      rw [(opening_path_registers state).2.1, nodePointer]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      change (node % 2^64) / 2 = (node/2) % 2^64
      rw [Nat.mod_eq_of_lt (by omega : node < 2^64), Nat.mod_eq_of_lt (by omega : node/2 < 2^64)]
    have nextData (slot : Nat) (slotBound : slot < 2^25) :
        readBuffer next (base+32*slot) 32 = heap slot := by
      rw [opening_path_preserves_digest state destination (base+32*slot) destinationPointer
        (by omega) (by omega) (by omega) (Or.inl (by omega))]
      exact data slot slotBound
    intro level inside
    rw [Function.iterate_succ_apply]
    cases level with
    | zero =>
      have retained : readBuffer (openingPathState^[count] next) destination 32 =
          readBuffer next destination 32 := by
        apply read_digest_congr _ _ _ destinationAligned
        intro i hi
        apply opening_path_loop_memory_below
        · rw [nextDestinationNat]; omega
        · rw [nextDestinationNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
      simp only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]
      rw [retained]
      rw [opening_path_digest state (base+32*(node ^^^ 1)) destination
        (by rw [heapPointer, nodePointer]; exact sibling_pointer base node)
        destinationPointer (by omega) destinationAligned (by omega) (by omega) (Or.inl (by omega))]
      exact data _ siblingBound
    | succ level =>
      have record := ih next (node/2) (destination+32) nextHeap nextNode nextDestination
        (by omega) (by omega) (by omega) (by omega) nextData level (by omega)
      have address : destination+32*(level+1) = destination+32+32*level := by omega
      rw [address]
      rw [Nat.div_div_eq_div_mul, show 2*2^level = 2^(level+1) by rw [Nat.pow_succ]; omega] at record
      exact record

end CommitGolfCandidate
