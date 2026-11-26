import CommitGolfCandidate.CommitRefinement
import CommitGolfCandidate.HeapLayout

/-! Every salted leaf digest stored by the 32-leaf unrolled commitment loop.
Leaf `i` lands at `heap + heapOffset i` of the gap heap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

attribute [local irreducible] commitBlockRun commitLeaves checkEvaluation

theorem commit_leaves_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitLeaves state (count + 1)) =
      let first := checkEvaluation oracle (commitBlockRun state)
      let rest := checkEvaluation oracle (commitLeaves first.1 count)
      (rest.1, first.2 + rest.2) := by
  rw [commitLeaves, check_evaluation_bind]

theorem commit_leaves_next_pointers (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat)
    (slotPointer : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap) :
    (checkEvaluation oracle (commitBlockRun state)).1.getReg .x10 = BitVec.ofNat 64 (slot + 8192) ∧
    (checkEvaluation oracle (commitBlockRun state)).1.getReg .x18 = BitVec.ofNat 64 (saltAddress + 512) ∧
    (checkEvaluation oracle (commitBlockRun state)).1.getReg .x23 = BitVec.ofNat 64 (heap + 1536) := by
  have regs := commit_block_registers state _ (check_evaluation_support oracle (commitBlockRun state))
  refine ⟨?_, ?_, ?_⟩
  · rw [regs.1, slotPointer, bitvec64_ofNat_add_lit]
  · rw [regs.2.1, saltPointer, bitvec64_ofNat_add_lit]
  · rw [regs.2.2.1, heapPointer, bitvec64_ofNat_add_lit]

theorem block_layout_of (state : MachineState) (slot saltAddress heap remaining : Nat)
    (slotPointer : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 24 + 8192 * (remaining + 1) ≤ heap)
    (saltsAfter : heap + 1536 * (remaining + 1) ≤ saltAddress)
    (bounded : saltAddress + 512 * (remaining + 1) ≤ MEMORY_BYTES) :
    BlockLayout state slot saltAddress heap :=
  ⟨slotPointer, saltPointer, heapPointer, slotAligned, saltAligned, heapAligned,
    by clear * - heapAfter; omega, by clear * - saltsAfter; omega,
    Nat.le_trans (by clear * -; omega) bounded⟩

/-- The whole 32-leaf block loop preserves any byte range outside its slot region and
outside every written leaf heap slot (in particular every pair's zero gap and all salts). -/
theorem commit_leaves_preserves (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap remaining address bytes : Nat)
    (slotPointer : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 24 + 8192 * remaining ≤ heap)
    (saltsAfter : heap + 1536 * remaining ≤ saltAddress)
    (bounded : saltAddress + 512 * remaining ≤ MEMORY_BYTES)
    (readBound : address + bytes ≤ 2^64)
    (outsideSlot : address + bytes ≤ slot ∨ slot + 8192 * remaining ≤ address)
    (outsideHeap : ∀ i < 32 * remaining,
      address + bytes ≤ heap + heapOffset i ∨ heap + heapOffset i + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 address bytes =
      readBuffer state address bytes := by
  induction remaining generalizing state slot saltAddress heap with
  | zero => rw [commitLeaves, check_evaluation_pure]
  | succ remaining ih =>
    have layout := block_layout_of state slot saltAddress heap remaining slotPointer saltPointer
      heapPointer slotAligned saltAligned heapAligned heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state slot saltAddress heap
      slotPointer saltPointer heapPointer
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitBlockRun state)).1 remaining)).1 address bytes = _
    rw [ih _ (slot + 8192) (saltAddress + 512) (heap + 1536) next.1 next.2.1 next.2.2
      (by clear * - slotAligned; omega) (by clear * - saltAligned; omega)
      (by clear * - heapAligned; omega) (by clear * - heapAfter; omega)
      (by clear * - saltsAfter; omega) (Nat.le_trans (by clear * -; omega) bounded)
      (by rcases outsideSlot with h | h <;> [exact Or.inl (by clear * - h; omega); exact Or.inr (by clear * - h; omega)])
      (by
        intro i hi
        have h := outsideHeap (i + 32) (by omega)
        have hOff : heapOffset (i + 32) = 1536 + heapOffset i := by unfold heapOffset; omega
        rw [hOff] at h
        rcases h with h | h <;> omega)]
    exact commit_block_preserves oracle state slot saltAddress heap address bytes layout
      readBound (by rcases outsideSlot with h | h <;> omega)
      (fun j hj => outsideHeap j (by omega))

/-- All heap leaf slots contain the position-tagged salted digest of the corresponding input. -/
theorem commit_leaves_digests (oracle : Oracle) (state : MachineState)
    (baseIdx heap saltAddress remaining : Nat) (idxBound : baseIdx + 32 * remaining ≤ LENGTH)
    (message : Nat → Entry) (salts : Nat → Salt)
    (slotPointer : state.getReg .x10 = BitVec.ofNat 64 (4072 + 256 * baseIdx))
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapAligned : heap % 8 = 0) (saltAligned : saltAddress % 8 = 0)
    (heapAfter : 4072 + 256 * baseIdx + 24 + 8192 * remaining ≤ heap)
    (saltsAfter : heap + 1536 * remaining ≤ saltAddress)
    (bounded : saltAddress + 512 * remaining ≤ MEMORY_BYTES)
    (headData : ∀ i < 32 * remaining,
      readBuffer state (4096 + 256 * (baseIdx + i)) 72 = (message i).extractLsb' 0 576)
    (blockData : ∀ i < 32 * remaining, ∀ b, 1 ≤ b → b < 4 →
      readBuffer state (4096 + 256 * (baseIdx + i) + 64 * b) 64 = (message i).extractLsb' (512 * b) 512)
    (saltData : ∀ i < 32 * remaining, readBuffer state (saltAddress + 16 * i) 16 = salts i) :
    ∀ index (hi : index < 32 * remaining),
      readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 (heap + heapOffset index) 32 =
        leafDigest oracle.compression ⟨baseIdx + index, by omega⟩ (salts index) (message index) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state baseIdx heap saltAddress message salts with
  | zero => intro index inside; omega
  | succ remaining ih =>
    have layout := block_layout_of state (4072 + 256 * baseIdx) saltAddress heap remaining
      slotPointer saltPointer heapPointer (by omega) saltAligned heapAligned
      heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state (4072 + 256 * baseIdx) saltAddress heap
      slotPointer saltPointer heapPointer
    have nextSlot : (checkEvaluation oracle (commitBlockRun state)).1.getReg .x10 =
        BitVec.ofNat 64 (4072 + 256 * (baseIdx + 32)) := by
      rw [next.1]
      exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
    have nextHead (i : Nat) (hi : i < 32 * remaining) :
        readBuffer (checkEvaluation oracle (commitBlockRun state)).1
          (4096 + 256 * (baseIdx + 32 + i)) 72 = (message (i + 32)).extractLsb' 0 576 := by
      rw [commit_block_preserves oracle state (4072 + 256 * baseIdx) saltAddress heap _ 72 layout
        (by omega) (Or.inr (by omega))
        (fun j hj => Or.inl (by have := heap_offset_bound j 16 (by omega); omega))]
      convert headData (i + 32) (by omega) using 2; omega
    have nextBlock (i : Nat) (hi : i < 32 * remaining) (b : Nat) (hb1 : 1 ≤ b) (hb4 : b < 4) :
        readBuffer (checkEvaluation oracle (commitBlockRun state)).1
          (4096 + 256 * (baseIdx + 32 + i) + 64 * b) 64 = (message (i + 32)).extractLsb' (512 * b) 512 := by
      rw [commit_block_preserves oracle state (4072 + 256 * baseIdx) saltAddress heap _ 64 layout
        (by omega) (Or.inr (by omega))
        (fun j hj => Or.inl (by have := heap_offset_bound j 16 (by omega); omega))]
      convert blockData (i + 32) (by omega) b hb1 hb4 using 2; omega
    have nextSalt (i : Nat) (hi : i < 32 * remaining) :
        readBuffer (checkEvaluation oracle (commitBlockRun state)).1
          (saltAddress + 512 + 16 * i) 16 = salts (i + 32) := by
      rw [commit_block_preserves oracle state (4072 + 256 * baseIdx) saltAddress heap _ 16 layout
        (by omega) (Or.inr (by omega))
        (fun j hj => Or.inr (by have := heap_offset_bound j 16 (by omega); omega))]
      convert saltData (i + 32) (by omega) using 2; omega
    have blk := commit_block_digests oracle state baseIdx saltAddress heap (by omega) layout
      message (fun k hk => headData k (by omega)) (fun k hk b hb1 hb4 => blockData k (by omega) b hb1 hb4)
    intro index inside
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitBlockRun state)).1 remaining)).1
        (heap + heapOffset index) 32 = _
    by_cases low : index < 32
    · have hOffIdx := heap_offset_bound index 16 (by omega)
      rw [commit_leaves_preserves oracle _ (4072 + 256 * (baseIdx + 32)) (saltAddress + 512)
        (heap + 1536) remaining (heap + heapOffset index) 32 nextSlot next.2.1 next.2.2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) (fun i _ => Or.inl (by omega))]
      rw [blk index low, saltData index (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, index = j + 32 := ⟨index - 32, by omega⟩
      have hrec := ih _ (baseIdx + 32) (heap + 1536) (saltAddress + 512) (by omega)
        (fun i => message (i + 32)) (fun i => salts (i + 32)) nextSlot next.2.2 next.2.1
        (by omega) (by omega) (by omega) (by omega) (by omega)
        nextHead nextBlock nextSalt j (by omega)
      have offset : heap + heapOffset (j + 32) = heap + 1536 + heapOffset j := by
        unfold heapOffset; omega
      have hidx : (⟨baseIdx + 32 + j, by omega⟩ : Index) = ⟨baseIdx + (j + 32), by omega⟩ := by
        apply Fin.ext; dsimp; omega
      rw [offset, ← hidx]
      exact hrec

end CommitGolfCandidate
