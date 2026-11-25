import CommitGolfCandidate.CommitRefinement

/-! Every salted leaf digest stored by the actual commitment leaf loop. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

attribute [local irreducible] commitPositionRun commitLeaves checkEvaluation

/-- Fixed-oracle evaluation of one leaf followed by the remaining leaf loop. -/
theorem commit_leaves_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitLeaves state (count+1)) =
      let first := checkEvaluation oracle (commitPositionRun state)
      let rest := checkEvaluation oracle (commitLeaves first.1 count)
      (rest.1, first.2+rest.2) := by
  rw [commitLeaves, check_evaluation_bind]

/-- The whole leaf loop preserves every digest outside its slot region and its
heap output range. -/
theorem commit_leaves_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot heap count address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 32 + 256*count ≤ MEMORY_BYTES)
    (heapBound : heap + 32*count ≤ 2^64)
    (aligned : address % 8 = 0) (readBound : address+32 ≤ 2^64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 256*count ≤ address)
    (outsideHeap : address + 32 ≤ heap ∨ heap + 32*count ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeaves state count)).1 address 32 =
      readBuffer state address 32 := by
  induction count generalizing state slot heap with
  | zero => rw [commitLeaves, check_evaluation_pure]
  | succ count ih =>
    have big := chain_memory_bound slot (by omega)
    rw [commit_leaves_evaluation]
    let next := (checkEvaluation oracle (commitPositionRun state)).1
    have regs := commit_position_registers state next (check_evaluation_support oracle _)
    have nextSlot : next.getReg .x8 = BitVec.ofNat 64 (slot+256) := by
      rw [regs.1, slotPointer, BitVec.ofNat_add]
      rfl
    have nextHeap : next.getReg .x23 = BitVec.ofNat 64 (heap+32) := by
      rw [regs.2.2.1, heapPointer, BitVec.ofNat_add]
      rfl
    change readBuffer (checkEvaluation oracle (commitLeaves next count)).1 address 32 = _
    rw [ih next (slot+256) (heap+32) nextSlot nextHeap (by omega) (by omega)
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega)]
    exact commit_position_preserves_digest oracle state slot heap address slotPointer heapPointer
      (by omega) (by omega) aligned readBound
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega)

set_option maxRecDepth 20000 in
/-- All heap leaf slots contain the salted hash of the corresponding original input.
The message vector (behind the first salt slot), leaf-output range, and salt range
occur in that order in memory. -/
theorem commit_leaves_digests (oracle : Oracle) (state : MachineState)
    (slot heap saltAddress count : Nat) (message : Nat → Entry) (salts : Nat → Digest)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (slotAligned : slot % 8 = 0) (heapAligned : heap % 8 = 0)
    (saltAligned : saltAddress % 8 = 0)
    (slotBound : slot + 32 + 256*count ≤ MEMORY_BYTES)
    (heapAfter : slot + 32 + 256*count ≤ heap)
    (saltsAfter : heap+32*count ≤ saltAddress)
    (bounded : saltAddress+32*count < 2^64)
    (data : ∀ index < count, ∀ block < 8,
      readBuffer state (slot+32+256*index+32*block) 32 = (message index).extractLsb' (256*block) 256)
    (saltData : ∀ index < count, readBuffer state (saltAddress+32*index) 32 = salts index) :
    ∀ index < count,
      readBuffer (checkEvaluation oracle (commitLeaves state count)).1 (heap+32*index) 32 =
        leafDigest oracle.compression (salts index) (message index) := by
  induction count generalizing state slot heap saltAddress message salts with
  | zero => intro index inside; omega
  | succ count ih =>
    have big := chain_memory_bound slot (by omega)
    let next := (checkEvaluation oracle (commitPositionRun state)).1
    have regs := commit_position_registers state next (check_evaluation_support oracle _)
    have nextSlot : next.getReg .x8 = BitVec.ofNat 64 (slot+256) := by
      rw [regs.1, slotPointer, BitVec.ofNat_add]
      rfl
    have nextHeap : next.getReg .x23 = BitVec.ofNat 64 (heap+32) := by
      rw [regs.2.2.1, heapPointer, BitVec.ofNat_add]
      rfl
    have nextSalt : next.getReg .x18 = BitVec.ofNat 64 (saltAddress+32) := by
      rw [regs.2.1, saltPointer, BitVec.ofNat_add]
      rfl
    have nextData (index : Nat) (inside : index < count) (block : Nat) (blockInside : block < 8) :
        readBuffer next (slot+256+32+256*index+32*block) 32 =
          (message (index+1)).extractLsb' (256*block) 256 := by
      rw [commit_position_preserves_digest oracle state slot heap (slot+256+32+256*index+32*block)
          slotPointer heapPointer (by omega) (by omega) (by omega) (by omega)
          (Or.inr (by omega)) (Or.inl (by omega))]
      convert data (index+1) (by omega) block blockInside using 1
      · congr 1
        omega
    have nextSaltData (index : Nat) (inside : index < count) :
        readBuffer next (saltAddress+32+32*index) 32 = salts (index+1) := by
      rw [commit_position_preserves_digest oracle state slot heap _ slotPointer heapPointer
        (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
      convert saltData (index+1) (by omega) using 1
      · congr 1
        omega
    intro index inside
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle (commitLeaves next count)).1 (heap+32*index) 32 = _
    cases index with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [commit_leaves_preserves_digest oracle next (slot+256) (heap+32) count heap
        nextSlot nextHeap (by omega) (by omega) heapAligned (by omega)
        (Or.inr (by omega)) (Or.inl (by omega))]
      rw [commit_position_digest oracle state slot saltAddress heap (message 0)
        slotPointer saltPointer heapPointer slotAligned saltAligned (by omega) (by omega)
        (Or.inr (by omega)) (by simpa using data 0 (by omega))]
      rw [← saltData 0 (by omega)]
      simp only [Nat.mul_zero, Nat.add_zero]
    | succ index =>
      have record := ih next (slot+256) (heap+32) (saltAddress+32)
        (fun i => message (i+1)) (fun i => salts (i+1)) nextSlot nextHeap nextSalt
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        nextData nextSaltData index (by omega)
      convert record using 1
      · congr 1
        omega

end CommitGolfCandidate
