import CommitGolfCandidate.CommitRefinement
import CommitGolfCandidate.HeapLayout

/-! Every salted leaf digest stored by the actual commitment leaf loop. The loop hashes
two leaves per iteration; leaf `i` lands at `heap + heapOffset i` of the gap heap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

attribute [local irreducible] commitPositionRun commitLeaves checkEvaluation

/-- Fixed-oracle evaluation of one pair followed by the remaining pair loop. -/
theorem commit_leaves_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitLeaves state (count+1)) =
      let first := checkEvaluation oracle (commitPositionRun state)
      let rest := checkEvaluation oracle (commitLeaves first.1 count)
      (rest.1, first.2+rest.2) := by
  rw [commitLeaves, check_evaluation_bind]

/-- Pointer advance of one evaluated pair iteration. -/
theorem commit_leaves_next_pointers (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap) :
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x8 = BitVec.ofNat 64 (slot+512) ∧
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x18 =
      BitVec.ofNat 64 (saltAddress+48) ∧
    (checkEvaluation oracle (commitPositionRun state)).1.getReg .x23 = BitVec.ofNat 64 (heap+96) := by
  have regs := commit_position_registers state _ (check_evaluation_support oracle (commitPositionRun state))
  refine ⟨?_, ?_, ?_⟩
  · rw [regs.1]; exact word_add_literal _ slot 512 slotPointer
  · rw [regs.2.1]; exact word_add_literal _ saltAddress 48 saltPointer
  · rw [regs.2.2.1]; exact word_add_literal _ heap 96 heapPointer

/-- The layout of pair `0` from the whole-loop layout hypotheses. -/
theorem pair_layout_of (state : MachineState) (slot saltAddress heap remaining : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 32 + 512*(remaining+1) ≤ heap)
    (saltsAfter : heap + 96*(remaining+1) ≤ saltAddress)
    (bounded : saltAddress + 48*(remaining+1) + 8 ≤ MEMORY_BYTES) :
    PairLayout state slot saltAddress heap :=
  ⟨slotPointer, saltPointer, heapPointer, slotAligned, saltAligned, heapAligned,
    by omega, by omega, by omega, Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩

/-- The whole pair loop preserves every digest outside its slot region and outside every
written heap pair; in particular every pair's zero gap `[heap+96p+64, heap+96p+96)`. -/
theorem commit_leaves_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap remaining address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (heapAfter : slot + 32 + 512*remaining ≤ heap)
    (saltsAfter : heap + 96*remaining ≤ saltAddress)
    (bounded : saltAddress + 48*remaining + 8 ≤ MEMORY_BYTES)
    (aligned : address % 8 = 0) (readBound : address+32 ≤ 2^64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 512*remaining ≤ address)
    (outsideHeap : ∀ p < remaining, address + 32 ≤ heap + 96*p ∨ heap + 96*p + 64 ≤ address) :
    readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 address 32 =
      readBuffer state address 32 := by
  induction remaining generalizing state slot saltAddress heap with
  | zero => rw [commitLeaves, check_evaluation_pure]
  | succ remaining ih =>
    have layout := pair_layout_of state slot saltAddress heap remaining slotPointer saltPointer
      heapPointer slotAligned saltAligned heapAligned heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state slot saltAddress heap
      slotPointer saltPointer heapPointer
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitPositionRun state)).1 remaining)).1 address 32 = _
    rw [ih _ (slot+512) (saltAddress+48) (heap+96) next.1 next.2.1 next.2.2
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rcases outsideSlot with h | h <;> omega)
      (by
        intro p hp
        have h := outsideHeap (p+1) (by omega)
        rcases h with h | h <;> omega)]
    exact commit_position_preserves_digest oracle state slot saltAddress heap address layout
      aligned readBound (by rcases outsideSlot with h | h <;> omega)
      (by have h := outsideHeap 0 (by omega); rcases h with h | h <;> omega)

/-- All heap leaf slots contain the salted hash of the corresponding original input.
The message vector (behind the first salt slot), leaf heap and salt range occur in that
order in memory. Leaf `i` is at `heap + heapOffset i`. -/
theorem commit_leaves_digests (oracle : Oracle) (state : MachineState)
    (slot heap saltAddress remaining : Nat) (message : Nat → Entry) (salts : Nat → BitVec 192)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (slotAligned : slot % 8 = 0) (heapAligned : heap % 8 = 0)
    (saltAligned : saltAddress % 8 = 0)
    (heapAfter : slot + 32 + 512*remaining ≤ heap)
    (saltsAfter : heap + 96*remaining ≤ saltAddress)
    (bounded : saltAddress + 48*remaining + 8 ≤ MEMORY_BYTES)
    (data : ∀ index < 2*remaining, ∀ block < 4,
      readBuffer state (slot+32+256*index+64*block) 64 = (message index).extractLsb' (512*block) 512)
    (saltData : ∀ index < 2*remaining, readBuffer state (saltAddress+24*index) 24 = salts index) :
    ∀ index < 2*remaining,
      readBuffer (checkEvaluation oracle (commitLeaves state remaining)).1 (heap+heapOffset index) 32 =
        leafDigest oracle.compression (saltState (salts index)) (message index) := by
  induction remaining generalizing state slot heap saltAddress message salts with
  | zero => intro index inside; omega
  | succ remaining ih =>
    have mem : MEMORY_BYTES = 2^36 := rfl
    have layout := pair_layout_of state slot saltAddress heap remaining slotPointer saltPointer
      heapPointer slotAligned saltAligned heapAligned heapAfter saltsAfter bounded
    have next := commit_leaves_next_pointers oracle state slot saltAddress heap
      slotPointer saltPointer heapPointer
    have nextData (index : Nat) (inside : index < 2*remaining) (block : Nat) (blockInside : block < 4) :
        readBuffer (checkEvaluation oracle (commitPositionRun state)).1
          (slot+512+32+256*index+64*block) 64 = (message (index+2)).extractLsb' (512*block) 512 := by
      rw [read_compression_halves _ _ (by omega),
        commit_position_preserves_digest oracle state slot saltAddress heap
          (slot+512+32+256*index+64*block+32) layout (by omega) (by omega)
          (Or.inr (by omega)) (Or.inl (by omega)),
        commit_position_preserves_digest oracle state slot saltAddress heap
          (slot+512+32+256*index+64*block) layout (by omega) (by omega)
          (Or.inr (by omega)) (Or.inl (by omega)),
        ← read_compression_halves _ _ (by omega)]
      convert data (index+2) (by omega) block blockInside using 2
      omega
    have nextSaltData (index : Nat) (inside : index < 2*remaining) :
        readBuffer (checkEvaluation oracle (commitPositionRun state)).1
          (saltAddress+48+24*index) 24 = salts (index+2) := by
      rw [commit_read_salt_of_digest _ state _ _ (commit_position_preserves_digest oracle state slot
        saltAddress heap _ layout (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]
      convert saltData (index+2) (by omega) using 2
      omega
    have pair := commit_position_digest oracle state slot saltAddress heap layout
      message (by
        intro k hk block hb
        convert data k (by omega) block hb using 2
        omega)
    intro index inside
    rw [commit_leaves_evaluation]
    change readBuffer (checkEvaluation oracle
      (commitLeaves (checkEvaluation oracle (commitPositionRun state)).1 remaining)).1
        (heap+heapOffset index) 32 = _
    by_cases low : index < 2
    · have offset : heapOffset index = 32*index := by unfold heapOffset; omega
      rw [offset, commit_leaves_preserves_digest oracle _ (slot+512) (saltAddress+48) (heap+96)
        remaining (heap+32*index) next.1 next.2.1 next.2.2 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
        (fun p _ => Or.inl (by omega))]
      rw [pair index low, saltData index (by omega)]
    · obtain ⟨j, rfl⟩ : ∃ j, index = j + 2 := ⟨index - 2, by omega⟩
      have record := ih _ (slot+512) (heap+96) (saltAddress+48)
        (fun i => message (i+2)) (fun i => salts (i+2)) next.1 next.2.2 next.2.1
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        nextData nextSaltData j (by omega)
      have offset : heap + heapOffset (j+2) = heap + 96 + heapOffset j := by
        unfold heapOffset; omega
      rw [offset]
      exact record

end CommitGolfCandidate
