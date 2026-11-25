import CommitGolfCandidate.OpeningRefinement

/-! Salt and sibling contents of complete opening iterations. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem prepared_memory (state : MachineState) :
    (openingPositionPreparedState state).mem = state.mem := rfl

private theorem path_memory (state : MachineState) :
    (openingPositionPathState state).mem =
      (openingCopyState (openingPositionPreparedState state)).mem := rfl

private theorem next_memory (state : MachineState) :
    (openingNextState state).mem = state.mem := rfl

private theorem salt_pointer (base index : Nat) :
    BitVec.ofNat 64 base + (BitVec.ofNat 64 index <<< 5) =
      BitVec.ofNat 64 (base+32*index) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 base + BitVec.ofNat 64 index * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index]

/-- The first record is the original private salt, copied by the actual image. -/
theorem opening_position_salt_copy (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x18 + (state.getMem (state.getReg .x24) <<< 5) =
      BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separated : source+32 ≤ destination) :
    readBuffer (openingPositionPathState state) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (path_memory state)]
  rw [opening_copy_digest _ source destination
    ((opening_position_prepared state).2.trans sourcePointer)
    ((opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)).trans
      destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound (Or.inl separated)]
  exact read_buffer_memory_congr _ _ (prepared_memory state) _ _

/-- Copying the salt preserves the heap and every earlier digest. -/
theorem opening_position_setup_preserves (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (bounded : destination+32 ≤ 2^64)
    (separated : address+32 ≤ destination) :
    readBuffer (openingPositionPathState state) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (path_memory state)]
  rw [opening_copy_preserves_digest _ destination address
    ((opening_position_prepare_register state .x25 (by decide) (by decide) (by decide)).trans
      destinationPointer) aligned bounded (by omega) (Or.inl separated)]
  exact read_buffer_memory_congr _ _ (prepared_memory state) _ _

/-- Every complete opening iteration emits the selected salt followed by the
24 siblings of the selected leaf. This states byte contents, not only output size. -/
theorem opening_position_records (state : MachineState) (heap : Nat → Digest)
    (base salts index destination : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 salts)
    (leafCount : state.getReg .x19 = BitVec.ofNat 64 LENGTH)
    (selected : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (heapAligned : base % 8 = 0) (saltAligned : salts % 8 = 0)
    (destinationAligned : destination % 8 = 0)
    (indexBound : index < LENGTH) (heapSeparated : base+3*2^29 ≤ destination)
    (saltSeparated : salts+2^29 ≤ destination) (bounded : destination+800 ≤ MEMORY_BYTES)
    (data : ∀ slot < 2^25, readBuffer state (base+heapOffset slot) 32 = heap slot) :
    readBuffer (openingPositionState state) destination 32 = readBuffer state (salts+32*index) 32 ∧
    ∀ level < 24, readBuffer (openingPositionState state) (destination+32+32*level) 32 =
      heap (((LENGTH+index)/2^level) ^^^ 1) := by
  let path := openingPositionPathState state
  have bound64 : destination+800 < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
  have indexSmall : index < 16777216 := indexBound
  have pathDestination : path.getReg .x25 = BitVec.ofNat 64 (destination+32) := by
    rw [(opening_position_path_registers state).1, destinationPointer]
    exact (BitVec.ofNat_add (n := 64) destination 32).symm
  have pathDestinationNat : (path.getReg .x25).toNat = destination+32 := by
    rw [pathDestination, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pathHeap : path.getReg .x9 = BitVec.ofNat 64 base :=
    (opening_position_path_register state .x9 (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans heapPointer
  have pathNode : path.getReg .x20 = BitVec.ofNat 64 (LENGTH+index) := by
    rw [(opening_position_path_registers state).2.1, selected, leafCount, ← BitVec.ofNat_add]
    rw [Nat.add_comm]
  have pathData (slot : Nat) (inside : slot < 2^25) :
      readBuffer path (base+heapOffset slot) 32 = heap slot := by
    have within := heap_offset_bound slot (2^24) (by omega)
    have aligned := heap_offset_aligned slot
    rw [opening_position_setup_preserves state destination (base+heapOffset slot)
      destinationPointer (by omega) (by omega) (by omega)]
    exact data slot inside
  have unchanged : ∀ address count,
      readBuffer (openingPositionState state) address count =
      readBuffer (openingPathState^[24] path) address count := by
    intro address count
    exact read_buffer_memory_congr _ _ (next_memory _) _ _
  constructor
  · rw [unchanged]
    have retained : readBuffer (openingPathState^[24] path) destination 32 =
        readBuffer path destination 32 := by
      apply read_digest_congr _ _ _ destinationAligned
      intro i hi
      apply opening_path_loop_memory_below
      · rw [pathDestinationNat]; omega
      · rw [pathDestinationNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    rw [retained]
    exact opening_position_salt_copy state (salts+32*index) destination
      (by rw [saltPointer, selected]; exact salt_pointer salts index)
      destinationPointer (by omega) destinationAligned (by omega) (by omega) (by omega)
  · intro level inside
    rw [unchanged]
    exact opening_path_records path heap base (LENGTH+index) (destination+32) 24
      pathHeap pathNode pathDestination heapAligned (by omega)
      (by change 16777216+index < 2^25; omega) (by omega) (by omega) pathData level inside

attribute [local irreducible] openingPositionState

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The outer opening loop preserves every memory word before its output buffer. -/
theorem opening_positions_memory_below (count : Nat) (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat+800*count ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    (openingPositionState^[count] state).getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    have nextOutput : ((openingPositionState state).getReg .x25).toNat =
        (state.getReg .x25).toNat+800 := by
      rw [(opening_position_progress state).2.1, BitVec.toNat_add]
      change ((state.getReg .x25).toNat+800) % 2^64 = _
      apply Nat.mod_eq_of_lt
      simp only [MEMORY_BYTES] at bounded
      omega
    rw [Function.iterate_succ_apply, ih]
    · exact opening_position_memory_below state address (by omega) below
    · rw [nextOutput]; omega
    · rw [nextOutput]; omega

/-- Each complete position preserves earlier digest buffers. -/
theorem opening_position_preserves_digest (state : MachineState) (destination address : Nat)
    (output : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (bounded : destination+800 ≤ MEMORY_BYTES)
    (separate : address+32 ≤ destination) :
    readBuffer (openingPositionState state) address 32 = readBuffer state address 32 := by
  have bound64 : destination+800 < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply opening_position_memory_below
  · rw [output, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact bounded
  · rw [output, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
      Nat.mod_eq_of_lt (by omega : destination < 2^64)]
    omega

/-- The complete outer loop emits every selected salt/path record, in index-list
order, and preserves each record while producing the later ones. -/
theorem opening_all_records (state : MachineState) (heap saltValue : Nat → Digest)
    (indices : Nat → Nat) (base salts indexAddress destination count : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 salts)
    (leafCount : state.getReg .x19 = BitVec.ofNat 64 LENGTH)
    (indexPointer : state.getReg .x24 = BitVec.ofNat 64 indexAddress)
    (outputPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (heapAligned : base % 8 = 0) (saltAligned : salts % 8 = 0)
    (outputAligned : destination % 8 = 0)
    (heapSeparated : base+3*2^29 ≤ destination) (saltSeparated : salts+2^29 ≤ destination)
    (indexSeparated : indexAddress+8*count ≤ destination)
    (bounded : destination+800*count ≤ MEMORY_BYTES)
    (indexData : ∀ ordinal < count,
      state.getMem (BitVec.ofNat 64 (indexAddress+8*ordinal)) = BitVec.ofNat 64 (indices ordinal))
    (indexBound : ∀ ordinal < count, indices ordinal < LENGTH)
    (heapData : ∀ slot < 2^25, readBuffer state (base+heapOffset slot) 32 = heap slot)
    (saltData : ∀ index < LENGTH, readBuffer state (salts+32*index) 32 = saltValue index) :
    ∀ ordinal < count,
      readBuffer (openingPositionState^[count] state) (destination+800*ordinal) 32 =
        saltValue (indices ordinal) ∧
      ∀ level < 24,
        readBuffer (openingPositionState^[count] state) (destination+800*ordinal+32+32*level) 32 =
          heap (((LENGTH+indices ordinal)/2^level) ^^^ 1) := by
  induction count generalizing state indices indexAddress destination with
  | zero => intro ordinal inside; omega
  | succ count ih =>
    have bound64 : destination+800*(count+1) < 2^64 := by
      simp only [MEMORY_BYTES] at bounded; omega
    let next := openingPositionState state
    have nextOutput : next.getReg .x25 = BitVec.ofNat 64 (destination+800) := by
      rw [(opening_position_progress state).2.1, outputPointer]
      exact (BitVec.ofNat_add (n := 64) destination 800).symm
    have nextOutputNat : (next.getReg .x25).toNat = destination+800 := by
      rw [nextOutput, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have nextIndex : next.getReg .x24 = BitVec.ofNat 64 (indexAddress+8) := by
      rw [(opening_position_progress state).1, indexPointer]
      exact (BitVec.ofNat_add (n := 64) indexAddress 8).symm
    have nextIndexData (ordinal : Nat) (inside : ordinal < count) :
        next.getMem (BitVec.ofNat 64 (indexAddress+8+8*ordinal)) =
          BitVec.ofNat 64 (indices (ordinal+1)) := by
      rw [opening_position_memory_below]
      · convert indexData (ordinal+1) (by omega) using 1
        congr 2
        omega
      · rw [outputPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      · rw [outputPointer, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : indexAddress+8+8*ordinal < 2^64),
          Nat.mod_eq_of_lt (by omega : destination < 2^64)]
        omega
    have nextHeapData (slot : Nat) (inside : slot < 2^25) :
        readBuffer next (base+heapOffset slot) 32 = heap slot := by
      have within := heap_offset_bound slot (2^24) (by omega)
      have aligned := heap_offset_aligned slot
      rw [opening_position_preserves_digest state destination (base+heapOffset slot)
        outputPointer (by omega) (by omega) (by omega)]
      exact heapData slot inside
    have nextSaltData (index : Nat) (inside : index < LENGTH) :
        readBuffer next (salts+32*index) 32 = saltValue index := by
      have small : index < 16777216 := inside
      rw [opening_position_preserves_digest state destination (salts+32*index)
        outputPointer (by omega) (by omega) (by omega)]
      exact saltData index inside
    intro ordinal inside
    rw [Function.iterate_succ_apply]
    cases ordinal with
    | zero =>
      have first := opening_position_records state heap base salts (indices 0) destination
        heapPointer saltPointer leafCount
        (by rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega))
        outputPointer heapAligned saltAligned outputAligned (indexBound 0 (by omega))
        heapSeparated saltSeparated (by omega) heapData
      have retained (offset : Nat) (aligned : offset % 8 = 0) (within : offset+32 ≤ 800) :
          readBuffer (openingPositionState^[count] next) (destination+offset) 32 =
            readBuffer next (destination+offset) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro i hi
        apply opening_positions_memory_below
        · rw [nextOutputNat]; omega
        · rw [nextOutputNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
      simp only [Nat.mul_zero, Nat.add_zero]
      constructor
      · rw [show destination = destination+0 by omega, retained 0 (by decide) (by decide)]
        exact Eq.trans first.1 (saltData (indices 0) (indexBound 0 (by omega)))
      · intro level levelBound
        rw [show destination+32+32*level = destination+(32+32*level) by omega,
          retained (32+32*level) (by omega) (by omega)]
        simpa only [Nat.add_assoc] using first.2 level levelBound
    | succ ordinal =>
      have record := ih next (fun k => indices (k+1)) (indexAddress+8) (destination+800)
        ((opening_position_bases state).1.trans heapPointer)
        ((opening_position_bases state).2.1.trans saltPointer)
        ((opening_position_bases state).2.2.trans leafCount)
        nextIndex nextOutput (by omega) (by omega) (by omega) (by omega) (by omega)
        nextIndexData (fun k hk => indexBound (k+1) (by omega)) nextHeapData nextSaltData
        ordinal (by omega)
      simpa only [show destination+800*(ordinal+1) = destination+800+800*ordinal by omega]
        using record

end CommitGolfCandidate
