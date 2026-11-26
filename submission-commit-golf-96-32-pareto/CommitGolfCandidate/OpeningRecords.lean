import CommitGolfCandidate.OpeningRefinement

/-! Salt, sibling, and cap-table contents of complete opening iterations. -/
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

/-- Every complete opening iteration emits the selected salt followed by `pathDepth`
siblings of the selected leaf. -/
theorem opening_position_records (pathDepth : Nat) (state : MachineState) (heap : Nat → Digest)
    (base salts index destination : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 salts)
    (leafCount : state.getReg .x19 = BitVec.ofNat 64 LENGTH)
    (selected : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (destinationPointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (heapAligned : base % 8 = 0) (saltAligned : salts % 8 = 0)
    (destinationAligned : destination % 8 = 0)
    (indexBound : index < LENGTH) (heapSeparated : base+3*2^29 ≤ destination)
    (saltSeparated : salts+2^29 ≤ destination)
    (bounded : destination+(32+32*pathDepth) ≤ MEMORY_BYTES)
    (data : ∀ slot < 2^25, readBuffer state (base+heapOffset slot) 32 = heap slot) :
    readBuffer (openingPositionState pathDepth state) destination 32 =
      readBuffer state (salts+32*index) 32 ∧
    ∀ level < pathDepth,
      readBuffer (openingPositionState pathDepth state) (destination+32+32*level) 32 =
        heap (((LENGTH+index)/2^level) ^^^ 1) := by
  let path := openingPositionPathState state
  have bound64 : destination+(32+32*pathDepth) < 2^64 := by
    simp only [MEMORY_BYTES] at bounded; omega
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
      readBuffer (openingPositionState pathDepth state) address count =
      readBuffer (openingPathState^[pathDepth] path) address count := by
    intro address count
    exact read_buffer_memory_congr _ _ (next_memory _) _ _
  constructor
  · rw [unchanged]
    have retained : readBuffer (openingPathState^[pathDepth] path) destination 32 =
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
    exact opening_path_records path heap base (LENGTH+index) (destination+32) pathDepth
      pathHeap pathNode pathDestination heapAligned (by omega)
      (by change 16777216+index < 2^25; omega) (by omega) (by omega) pathData level inside

attribute [local irreducible] openingPositionState

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The outer opening loop preserves every memory word before its output buffer. -/
theorem opening_positions_memory_below (pathDepth count : Nat) (state : MachineState) (address : Word)
    (bounded : (state.getReg .x25).toNat+(32+32*pathDepth)*count ≤ MEMORY_BYTES)
    (below : address.toNat < (state.getReg .x25).toNat) :
    ((openingPositionState pathDepth)^[count] state).getMem address = state.getMem address := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    have recordLe : (state.getReg .x25).toNat + (32 + 32 * pathDepth) ≤ MEMORY_BYTES := by
      have : (32 + 32 * pathDepth) * 1 ≤ (32 + 32 * pathDepth) * (count + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have nextOutput : ((openingPositionState pathDepth state).getReg .x25).toNat =
        (state.getReg .x25).toNat+(32+32*pathDepth) := by
      rw [(opening_position_progress pathDepth state).2.1, BitVec.toNat_add, BitVec.toNat_ofNat]
      simp only [MEMORY_BYTES] at recordLe
      rw [Nat.mod_eq_of_lt (by omega : 32 + 32 * pathDepth < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)]
    rw [Function.iterate_succ_apply, ih]
    · exact opening_position_memory_below pathDepth state address recordLe below
    · rw [nextOutput]; rw [Nat.mul_succ] at bounded; omega
    · rw [nextOutput]; omega

/-- Each complete position preserves earlier digest buffers. -/
theorem opening_position_preserves_digest (pathDepth : Nat) (state : MachineState)
    (destination address : Nat)
    (output : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0) (bounded : destination+(32+32*pathDepth) ≤ MEMORY_BYTES)
    (separate : address+32 ≤ destination) :
    readBuffer (openingPositionState pathDepth state) address 32 = readBuffer state address 32 := by
  have bound64 : destination+(32+32*pathDepth) < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply opening_position_memory_below pathDepth
  · rw [output, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact bounded
  · rw [output, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : address+8*i < 2^64),
      Nat.mod_eq_of_lt (by omega : destination < 2^64)]
    omega

/-- The complete outer loop emits every selected salt/path record, in index-list
order, and preserves each record while producing the later ones. -/
theorem opening_all_records (pathDepth : Nat) (state : MachineState)
    (heap saltValue : Nat → Digest)
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
    (bounded : destination+(32+32*pathDepth)*count ≤ MEMORY_BYTES)
    (indexData : ∀ ordinal < count,
      state.getMem (BitVec.ofNat 64 (indexAddress+8*ordinal)) = BitVec.ofNat 64 (indices ordinal))
    (indexBound : ∀ ordinal < count, indices ordinal < LENGTH)
    (heapData : ∀ slot < 2^25, readBuffer state (base+heapOffset slot) 32 = heap slot)
    (saltData : ∀ index < LENGTH, readBuffer state (salts+32*index) 32 = saltValue index) :
    ∀ ordinal < count,
      readBuffer ((openingPositionState pathDepth)^[count] state)
        (destination+(32+32*pathDepth)*ordinal) 32 = saltValue (indices ordinal) ∧
      ∀ level < pathDepth,
        readBuffer ((openingPositionState pathDepth)^[count] state)
          (destination+(32+32*pathDepth)*ordinal+32+32*level) 32 =
            heap (((LENGTH+indices ordinal)/2^level) ^^^ 1) := by
  induction count generalizing state indices indexAddress destination with
  | zero => intro ordinal inside; omega
  | succ count ih =>
    have recordLe : destination+(32+32*pathDepth) ≤ MEMORY_BYTES := by
      have : (32+32*pathDepth)*1 ≤ (32+32*pathDepth)*(count+1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have bound64 : destination+(32+32*pathDepth)*(count+1) < 2^64 := by
      simp only [MEMORY_BYTES] at bounded; omega
    let next := openingPositionState pathDepth state
    have nextOutput : next.getReg .x25 = BitVec.ofNat 64 (destination+(32+32*pathDepth)) := by
      rw [(opening_position_progress pathDepth state).2.1, outputPointer]
      exact (BitVec.ofNat_add (n := 64) destination (32+32*pathDepth)).symm
    have rec64 : destination + (32 + 32 * pathDepth) < 2 ^ 64 := by
      simp only [MEMORY_BYTES] at recordLe; omega
    have nextOutputNat : (next.getReg .x25).toNat = destination+(32+32*pathDepth) := by
      rw [nextOutput, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rec64]
    have nextIndex : next.getReg .x24 = BitVec.ofNat 64 (indexAddress+8) := by
      rw [(opening_position_progress pathDepth state).1, indexPointer]
      exact (BitVec.ofNat_add (n := 64) indexAddress 8).symm
    have nextIndexData (ordinal : Nat) (inside : ordinal < count) :
        next.getMem (BitVec.ofNat 64 (indexAddress+8+8*ordinal)) =
          BitVec.ofNat 64 (indices (ordinal+1)) := by
      rw [opening_position_memory_below pathDepth]
      · convert indexData (ordinal+1) (by omega) using 1
        congr 2; omega
      · rw [outputPointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact recordLe
      · rw [outputPointer, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : indexAddress+8+8*ordinal < 2^64),
          Nat.mod_eq_of_lt (by omega : destination < 2^64)]
        omega
    have nextHeapData (slot : Nat) (inside : slot < 2^25) :
        readBuffer next (base+heapOffset slot) 32 = heap slot := by
      have within := heap_offset_bound slot (2^24) (by omega)
      have aligned := heap_offset_aligned slot
      rw [opening_position_preserves_digest pathDepth state destination (base+heapOffset slot)
        outputPointer (by omega) recordLe (by omega)]
      exact heapData slot inside
    have nextSaltData (index : Nat) (inside : index < LENGTH) :
        readBuffer next (salts+32*index) 32 = saltValue index := by
      have small : index < 16777216 := inside
      rw [opening_position_preserves_digest pathDepth state destination (salts+32*index)
        outputPointer (by omega) recordLe (by omega)]
      exact saltData index inside
    intro ordinal inside
    rw [Function.iterate_succ_apply]
    cases ordinal with
    | zero =>
      have first := opening_position_records pathDepth state heap base salts (indices 0) destination
        heapPointer saltPointer leafCount
        (by rw [indexPointer]; simpa only [Nat.mul_zero, Nat.add_zero] using indexData 0 (by omega))
        outputPointer heapAligned saltAligned outputAligned (indexBound 0 (by omega))
        heapSeparated saltSeparated recordLe heapData
      have retained (offset : Nat) (aligned : offset % 8 = 0) (within : offset+32 ≤ 32+32*pathDepth) :
          readBuffer ((openingPositionState pathDepth)^[count] next) (destination+offset) 32 =
            readBuffer next (destination+offset) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro i hi
        apply opening_positions_memory_below pathDepth
        · rw [nextOutputNat]; rw [Nat.mul_succ] at bounded; omega
        · rw [nextOutputNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
      simp only [Nat.mul_zero, Nat.add_zero]
      constructor
      · rw [show destination = destination+0 by omega, retained 0 (by decide) (by omega)]
        exact Eq.trans first.1 (saltData (indices 0) (indexBound 0 (by omega)))
      · intro level levelBound
        rw [show destination+32+32*level = destination+(32+32*level) by omega,
          retained (32+32*level) (by omega) (by omega)]
        simpa only [Nat.add_assoc] using first.2 level levelBound
    | succ ordinal =>
      have record := ih next (fun k => indices (k+1)) (indexAddress+8) (destination+(32+32*pathDepth))
        ((opening_position_bases pathDepth state).1.trans heapPointer)
        ((opening_position_bases pathDepth state).2.1.trans saltPointer)
        ((opening_position_bases pathDepth state).2.2.trans leafCount)
        nextIndex nextOutput (by omega) (by omega) (by omega) (by omega)
        (by rw [Nat.mul_succ] at bounded; omega)
        nextIndexData (fun k hk => indexBound (k+1) (by omega)) nextHeapData nextSaltData
        ordinal (by omega)
      simpa only [show destination+(32+32*pathDepth)*(ordinal+1) =
          destination+(32+32*pathDepth)+(32+32*pathDepth)*ordinal by rw [Nat.mul_succ]; omega]
        using record

/-! ### Level-7 cap-table copy contents -/

private theorem cap_pair_first_copy (state : MachineState) (src dst : Nat)
    (srcPtr : state.getReg .x23 = BitVec.ofNat 64 src)
    (dstPtr : state.getReg .x25 = BitVec.ofNat 64 dst)
    (srcAligned : src % 8 = 0) (dstAligned : dst % 8 = 0)
    (srcBound : src + 64 ≤ MEMORY_BYTES) (dstBound : dst + 64 ≤ MEMORY_BYTES)
    (separated : src + 64 ≤ dst) :
    readBuffer (openingCapPairState state) dst 32 = readBuffer state src 32 ∧
    readBuffer (openingCapPairState state) (dst + 32) 32 = readBuffer state (src + 32) 32 := by
  have src64 : src + 64 < 2^64 := by simp only [MEMORY_BYTES] at srcBound; omega
  have dst64 : dst + 64 < 2^64 := by simp only [MEMORY_BYTES] at dstBound; omega
  let c1 := openingCopyState state
  let m := openingCapMidState c1
  let c2 := openingCopyState m
  have pairMem : (openingCapPairState state).mem = c2.mem := rfl
  have midMem : m.mem = c1.mem := rfl
  have mSrc : m.getReg .x23 = BitVec.ofNat 64 (src + 32) := by
    simp only [m, openingCapMidState, c1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x23),
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0),
      opening_copy_register _ .x23 (by decide), srcPtr]
    exact (BitVec.ofNat_add src 32).symm
  have mDst : m.getReg .x25 = BitVec.ofNat 64 (dst + 32) := by
    simp only [m, openingCapMidState, c1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
      opening_copy_register _ .x25 (by decide), dstPtr]
    exact (BitVec.ofNat_add dst 32).symm
  constructor
  · rw [read_buffer_memory_congr _ _ pairMem,
      opening_copy_preserves_digest m (dst + 32) dst mDst dstAligned (by omega) (by omega) (Or.inl (by omega)),
      read_buffer_memory_congr _ _ midMem,
      opening_copy_digest state src dst srcPtr dstPtr srcAligned dstAligned (by omega) (by omega) (Or.inl (by omega))]
  · rw [read_buffer_memory_congr _ _ pairMem,
      opening_copy_digest m (src + 32) (dst + 32) mSrc mDst (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)),
      read_buffer_memory_congr _ _ midMem,
      opening_copy_preserves_digest state dst (src + 32) dstPtr (by omega) (by omega) (by omega) (Or.inl (by omega))]

private theorem cap_pair_preserves_digest (state : MachineState) (dst address : Nat)
    (dstPtr : state.getReg .x25 = BitVec.ofNat 64 dst)
    (aligned : address % 8 = 0) (bounded : dst + 64 ≤ MEMORY_BYTES)
    (separate : address + 32 ≤ dst) :
    readBuffer (openingCapPairState state) address 32 = readBuffer state address 32 := by
  have bound64 : dst + 64 < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply opening_cap_pair_memory_below
  · rw [dstPtr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact bounded
  · rw [dstPtr, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : address + 8*i < 2^64),
      Nat.mod_eq_of_lt (by omega : dst < 2^64)]
    omega

/-- The cap loop copies `count` consecutive gap-heap pairs (`2 * count` digests)
starting at `src` into contiguous 64-byte slots starting at `dst`. -/
theorem opening_cap_records (state : MachineState) (capVal : Nat → Digest)
    (src dst count : Nat)
    (srcPtr : state.getReg .x23 = BitVec.ofNat 64 src)
    (dstPtr : state.getReg .x25 = BitVec.ofNat 64 dst)
    (srcAligned : src % 8 = 0) (dstAligned : dst % 8 = 0)
    (separated : src + 96 * count ≤ dst)
    (bounded : dst + 64 * count ≤ MEMORY_BYTES)
    (capData : ∀ p < count,
      readBuffer state (src + 96 * p) 32 = capVal (2 * p) ∧
      readBuffer state (src + 96 * p + 32) 32 = capVal (2 * p + 1)) :
    ∀ p < count,
      readBuffer (openingCapPairState^[count] state) (dst + 64 * p) 32 = capVal (2 * p) ∧
      readBuffer (openingCapPairState^[count] state) (dst + 64 * p + 32) 32 = capVal (2 * p + 1) := by
  induction count generalizing state capVal src dst with
  | zero => intro p hp; omega
  | succ count ih =>
    have bound64 : dst + 64 * (count + 1) < 2^64 := by simp only [MEMORY_BYTES] at bounded; omega
    let next := openingCapPairState state
    have nextSrc : next.getReg .x23 = BitVec.ofNat 64 (src + 96) := by
      rw [(opening_cap_pair_registers state).1, srcPtr]
      exact (BitVec.ofNat_add src 96).symm
    have nextDst : next.getReg .x25 = BitVec.ofNat 64 (dst + 64) := by
      rw [(opening_cap_pair_registers state).2.1, dstPtr]
      exact (BitVec.ofNat_add dst 64).symm
    have nextDstNat : (next.getReg .x25).toNat = dst + 64 := by
      rw [nextDst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have nextData (p : Nat) (hp : p < count) :
        readBuffer next (src + 96 + 96 * p) 32 = capVal (2 * (p + 1)) ∧
        readBuffer next (src + 96 + 96 * p + 32) 32 = capVal (2 * (p + 1) + 1) := by
      have d := capData (p + 1) (by omega)
      constructor
      · rw [cap_pair_preserves_digest state dst _ dstPtr (by omega) (by omega) (by omega)]
        simpa only [show src + 96 + 96 * p = src + 96 * (p + 1) by omega] using d.1
      · rw [cap_pair_preserves_digest state dst _ dstPtr (by omega) (by omega) (by omega)]
        simpa only [show src + 96 + 96 * p + 32 = src + 96 * (p + 1) + 32 by omega] using d.2
    intro p hp
    rw [Function.iterate_succ_apply]
    cases p with
    | zero =>
      have first := cap_pair_first_copy state src dst srcPtr dstPtr srcAligned dstAligned
        (by omega) (by omega) (by omega)
      have d0 := capData 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at d0 ⊢
      have retained (off : Nat) (ho : off % 8 = 0) (hb : off + 32 ≤ 64) :
          readBuffer (openingCapPairState^[count] next) (dst + off) 32 =
            readBuffer next (dst + off) 32 := by
        apply read_digest_congr _ _ _ (by omega)
        intro i hi
        apply opening_cap_loop_memory_below
        · rw [nextDstNat]; omega
        · rw [nextDstNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      constructor
      · rw [show dst = dst + 0 by omega, retained 0 (by decide) (by decide)]
        exact first.1.trans d0.1
      · rw [retained 32 (by decide) (by decide)]
        exact first.2.trans d0.2
    | succ p =>
      have hRec := ih next (fun k => capVal (k + 2)) (src + 96) (dst + 64)
        nextSrc nextDst (by omega) (by omega) (by omega) (by omega)
        (fun q hq => by
          simpa only [show 2 * q + 2 = 2 * (q + 1) by omega,
            show 2 * q + 1 + 2 = 2 * (q + 1) + 1 by omega] using nextData q hq)
        p (by omega)
      simpa only [show dst + 64 * (p + 1) = dst + 64 + 64 * p by omega,
        show 2 * p + 2 = 2 * (p + 1) by omega,
        show 2 * p + 1 + 2 = 2 * (p + 1) + 1 by omega] using hRec

end CommitGolfCandidate
