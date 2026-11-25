import CommitGolfCandidate.CommitRefinement
import CommitGolfCandidate.HeapLayout

/-! Every salted leaf digest stored by the actual commitment leaf loop. The loop hashes
32 leaves per iteration; leaf `i` lands at `heap + heapOffset i` of the gap heap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

attribute [local irreducible] commitPositionRun commitLeaves checkEvaluation

/-- Fixed-oracle evaluation of one 32-leaf iteration followed by the remaining loop. -/
theorem commit_leaves_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitLeaves state (count + 1)) =
      let first := checkEvaluation oracle (commitPositionRun state)
      let rest := checkEvaluation oracle (commitLeaves first.1 count)
      (rest.1, first.2 + rest.2) := by
  rw [commitLeaves, check_evaluation_bind]

/-- Pointer advance of one evaluated 32-leaf iteration. -/
theorem commit_leaves_next_pointers (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (r29 : state.getReg .x29 = 2048) :
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x8 = BitVec.ofNat 64 (slot + 8192) ∧
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x18 =
      BitVec.ofNat 64 (saltAddress + 1024) ∧
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x23 = BitVec.ofNat 64 (heap + 1536) ∧
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x29 = 2048 := by
  have regs := commit_position_registers state _ r29
    (check_evaluation_support oracle (commitPositionRun state))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [regs.1]; exact word_add_literal _ slot 8192 slotPointer
  · rw [regs.2.1]; exact word_add_literal _ saltAddress 1024 saltPointer
  · rw [regs.2.2.1]; exact word_add_literal _ heap 1536 heapPointer
  · exact (regs.2.2.2.2.2 .x29 (by simp)).trans r29

/-- The layout of the first 32-leaf block from the whole-loop layout hypotheses. -/
theorem pair_layout_of (state : MachineState) (slot saltAddress heap remaining : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (r29 : state.getReg .x29 = 2048)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 32 + 8192 * (remaining + 1) ≤ heap)
    (saltsAfter : heap + 1536 * (remaining + 1) ≤ saltAddress)
    (bounded : saltAddress + 1024 * (remaining + 1) ≤ MEMORY_BYTES) :
    PairLayout state slot saltAddress heap := by
  have h1 : 8192 ≤ 8192 * (remaining + 1) := Nat.le_mul_of_pos_right 8192 (Nat.succ_pos remaining)
  have h2 : 1536 ≤ 1536 * (remaining + 1) := Nat.le_mul_of_pos_right 1536 (Nat.succ_pos remaining)
  have h3 : 1024 ≤ 1024 * (remaining + 1) := Nat.le_mul_of_pos_right 1024 (Nat.succ_pos remaining)
  generalize 8192 * (remaining + 1) = k1 at heapAfter h1
  generalize 1536 * (remaining + 1) = k2 at saltsAfter h2
  generalize 1024 * (remaining + 1) = k3 at bounded h3
  exact ⟨slotPointer, saltPointer, heapPointer, r29, slotAligned, saltAligned, heapAligned,
    by omega, by omega, by omega, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

/-- The whole 32-leaf loop preserves every digest outside its slot region and outside every
written heap pair; in particular every pair's zero gap `[heap + 96*p + 64, heap + 96*p + 96)`. -/
theorem commit_leaves_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap remaining address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (r29 : state.getReg .x29 = 2048)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 32 + 8192 * remaining ≤ heap)
    (saltsAfter : heap + 1536 * remaining ≤ saltAddress)
    (bounded : saltAddress + 1024 * remaining ≤ MEMORY_BYTES)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2 ^ 64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 8192 * remaining ≤ address)
    (outsideHeap : ∀ p < 16 * remaining,
      address + 32 ≤ heap + 96 * p ∨ heap + 96 * p + 64 ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 address 32 =
      readBuffer state address 32 := by
  induction remaining generalizing state slot saltAddress heap with
  | zero => rw [commitLeaves, check_evaluation_pure]
  | succ remaining ih =>
    have layout := pair_layout_of state slot saltAddress heap remaining slotPointer saltPointer
      heapPointer r29 slotAligned saltAligned heapAligned heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state slot saltAddress heap
      slotPointer saltPointer heapPointer r29
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitPositionRun state)).1 remaining)).1 address 32 = _
    rw [ih _ (slot + 8192) (saltAddress + 1024) (heap + 1536) next.1 next.2.1 next.2.2.1 next.2.2.2
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rcases outsideSlot with h | h <;> omega)
      (by
        intro p hp
        have h := outsideHeap (p + 16) (by omega)
        rcases h with h | h <;> omega)]
    exact commit_position_preserves_digest oracle state slot saltAddress heap address layout
      aligned readBound (by rcases outsideSlot with h | h <;> omega)
      (fun i hi => by
        have h := outsideHeap (i / 2) (by omega)
        have hoff : heapOffset i = 96 * (i / 2) + 32 * (i % 2) := by unfold heapOffset; omega
        rcases h with h | h <;> omega)

/-- All heap leaf slots contain the salted hash of the corresponding original input.
Leaf `i` is at `heap + heapOffset i`. -/
theorem commit_leaves_digests (oracle : Oracle) (state : MachineState)
    (slot heap saltAddress remaining : Nat) (message : Nat → Entry) (salts : Nat → Digest)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (r29 : state.getReg .x29 = 2048)
    (slotAligned : slot % 8 = 0) (heapAligned : heap % 8 = 0)
    (saltAligned : saltAddress % 8 = 0)
    (heapAfter : slot + 32 + 8192 * remaining ≤ heap)
    (saltsAfter : heap + 1536 * remaining ≤ saltAddress)
    (bounded : saltAddress + 1024 * remaining ≤ MEMORY_BYTES)
    (data : ∀ index < 32 * remaining, ∀ block < 4,
      readBuffer state (slot + 32 + 256 * index + 64 * block) 64 =
        (message index).extractLsb' (512 * block) 512)
    (saltData : ∀ index < 32 * remaining, readBuffer state (saltAddress + 32 * index) 32 = salts index) :
    ∀ index < 32 * remaining,
      readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 (heap + heapOffset index) 32 =
        leafDigest oracle.compression (salts index) (message index) := by
  induction remaining generalizing state slot heap saltAddress message salts with
  | zero => intro index inside; omega
  | succ remaining ih =>
    have mem : MEMORY_BYTES = 2 ^ 36 := rfl
    have layout := pair_layout_of state slot saltAddress heap remaining slotPointer saltPointer
      heapPointer r29 slotAligned saltAligned heapAligned heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state slot saltAddress heap
      slotPointer saltPointer heapPointer r29
    have nextData (index : Nat) (inside : index < 32 * remaining) (block : Nat) (blockInside : block < 4) :
        readBuffer (checkEvaluation oracle (commitPositionRun state)).1
          (slot + 8192 + 32 + 256 * index + 64 * block) 64 =
            (message (index + 32)).extractLsb' (512 * block) 512 := by
      rw [read_compression_halves _ _ (by omega),
        commit_position_preserves_digest oracle state slot saltAddress heap
          (slot + 8192 + 32 + 256 * index + 64 * block + 32) layout (by omega) (by omega)
          (Or.inr (by omega)) (fun i hi => Or.inl (by unfold heapOffset; omega)),
        commit_position_preserves_digest oracle state slot saltAddress heap
          (slot + 8192 + 32 + 256 * index + 64 * block) layout (by omega) (by omega)
          (Or.inr (by omega)) (fun i hi => Or.inl (by unfold heapOffset; omega)),
        ← read_compression_halves _ _ (by omega)]
      rw [show slot + 8192 + 32 + 256 * index + 64 * block =
        slot + 32 + 256 * (index + 32) + 64 * block by omega]
      exact data (index + 32) (by omega) block blockInside
    have nextSaltData (index : Nat) (inside : index < 32 * remaining) :
        readBuffer (checkEvaluation oracle (commitPositionRun state)).1
          (saltAddress + 1024 + 32 * index) 32 = salts (index + 32) := by
      rw [commit_position_preserves_digest oracle state slot saltAddress heap _ layout
        (by omega) (by omega) (Or.inr (by omega))
        (fun i hi => Or.inr (by unfold heapOffset; omega))]
      rw [show saltAddress + 1024 + 32 * index = saltAddress + 32 * (index + 32) by omega]
      exact saltData (index + 32) (by omega)
    have block := commit_position_digest oracle state slot saltAddress heap layout message (by
      intro i hi block hb
      rw [show slot + 256 * i + 32 + 64 * block = slot + 32 + 256 * i + 64 * block by omega]
      exact data i (by omega) block hb)
    intro index inside
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitPositionRun state)).1 remaining)).1
        (heap + heapOffset index) 32 = _
    by_cases low : index < 32
    · have hOff : heapOffset index + 32 ≤ 1536 := by unfold heapOffset; omega
      have hAlign : heapOffset index % 8 = 0 := heap_offset_aligned index
      rw [commit_leaves_preserves_digest oracle _ (slot + 8192) (saltAddress + 1024) (heap + 1536)
        remaining (heap + heapOffset index) next.1 next.2.1 next.2.2.1 next.2.2.2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) (fun p _ => Or.inl (by omega))]
      rw [block index low, saltData index (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, index = j + 32 := ⟨index - 32, by omega⟩
      have record := ih _ (slot + 8192) (heap + 1536) (saltAddress + 1024)
        (fun i => message (i + 32)) (fun i => salts (i + 32))
        next.1 next.2.2.1 next.2.1 next.2.2.2
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        nextData nextSaltData j (by omega)
      have offset : heap + heapOffset (j + 32) = heap + 1536 + heapOffset j := by
        unfold heapOffset; omega
      rw [offset]
      exact record

end CommitGolfCandidate
