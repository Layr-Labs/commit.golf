import CommitGolfCandidate.CursorSaltExecution
import CommitGolfCandidate.CursorOuterFrame
import CommitGolfCandidate.ContiguousLatch
import CommitGolfCandidate.ContiguousPC
import CommitGolfCandidate.FusedTail

/-! One contiguous iteration copies salt through x10 and falls directly into the
eight-block leaf, then advances salt/heap pointers in the relocated heap latch. The
reference still supplies virtual progress for memory refinement. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The complete physical position uses 35 instructions, 91 cycles and eight
queries. Delivered-image fetch premises remain explicit until image assembly. -/
theorem contiguous_position (saltFetched : ContiguousSaltFetched (submission.image .commit))
    (prefixFetched : ContiguousPrefixFetched (submission.image .commit))
    (tailFetched : ContiguousTailFetched (submission.image .commit))
    (latchFetched : ContiguousLatchFetched (submission.image .commit))
    (state : MachineState) (messageBase : Word) (pc : state.pc = 4280)
    (link : state.getReg .x1 = 4316)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (above : 32 ≤ (state.getReg .x8).toNat)
    (oracleReady : CommitLeafOracleReady state)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (remaining : Nat)
    (window : (state.getReg .x23).toNat + 32 * (remaining + 1) =
      (state.getReg .x22).toNat) (fuel : Nat) :
    execute (submission.image .commit) (35 + fuel) (cursorNormalize state messageBase 4456) true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize finished messageBase (if remaining = 0 then 4596 else 4456)) true
          return result.charge 91 8) := by
  let cursor := (state.getReg .x8).toNat - 32
  let ready := commitPositionState state
  obtain ⟨aligned, bounded⟩ := commit_leaf_source_range state messageValid
  have chain : state.getReg .x21 = BitVec.ofNat 64 cursor := by
    rw [scratch]
    calc
      state.getReg .x8 - 32 = BitVec.ofNat 64 (state.getReg .x8).toNat -
          BitVec.ofNat 64 32 := by simp
      _ = _ := BitVec.ofNat_sub_ofNat_of_le (w := 64) _ 32 (by decide) above
  have source : state.getReg .x8 = BitVec.ofNat 64 (cursor + 32) := by
    have natural : cursor + 32 = (state.getReg .x8).toNat := by dsimp [cursor]; omega
    rw [natural]; simp
  have destinationValid : ∀ word : Fin 4,
      accessValid ((cursorNormalize state messageBase 4456).getReg .x10 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    change accessValid ((cursorLeafFrame state messageBase).getReg .x10 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true
    rw [cursor_frame_pointer, chain, ← BitVec.ofNat_add]
    have small : cursor + 8 * word.val < 2 ^ 64 := by
      have hw := word.isLt
      dsimp [cursor]
      unfold MEMORY_BYTES at bounded
      omega
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have hw := word.isLt; dsimp [cursor]; omega
    · dsimp [cursor]; omega
  have physicalSalt : ∀ word : Fin 4,
      accessValid ((cursorNormalize state messageBase 4456).getReg .x18 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    change ∀ word : Fin 4, accessValid ((cursorLeafFrame state messageBase).getReg .x18 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true
    rw [cursor_frame_register state messageBase .x18 (by decide)]
    exact saltValid
  have readySource : ready.getReg .x8 = state.getReg .x8 :=
    commit_position_register state .x8 (by decide) (by decide)
  have readyChain : ready.getReg .x21 = BitVec.ofNat 64 cursor :=
    (commit_position_register state .x21 (by decide) (by decide)).trans chain
  have readyOracle : StreamingOracleReady (cursorLeafFrame ready messageBase) := by
    rcases oracleReady with ⟨r5, r11, r13⟩
    exact ⟨(cursor_frame_register ready messageBase .x5 (by decide)).trans
        ((commit_position_register state .x5 (by decide) (by decide)).trans r5),
      (cursor_frame_register ready messageBase .x11 (by decide)).trans
        ((commit_position_register state .x11 (by decide) (by decide)).trans r11),
      (cursor_frame_register ready messageBase .x13 (by decide)).trans
        ((commit_position_register state .x13 (by decide) (by decide)).trans r13)⟩
  have readyHeap : rangeValid ((cursorLeafFrame ready messageBase).getReg .x23) 32 = true ∧
      ((cursorLeafFrame ready messageBase).getReg .x23).toNat % 8 = 0 := by
    rw [cursor_frame_register ready messageBase .x23 (by decide),
      commit_position_register state .x23 (by decide) (by decide)]
    exact commit_leaf_heap_range state heapValid
  have leafRun := contiguous_leaf_blocks (submission.image .commit) prefixFetched tailFetched
    ((cursorLeafFrame ready messageBase).setPC 4488) cursor rfl
    (by rw [MachineState.getReg_setPC, cursor_frame_pointer]; exact readyChain)
    (by simpa only [StreamingOracleReady, MachineState.getReg_setPC] using readyOracle)
    (by dsimp [cursor]; omega) (by dsimp [cursor]; omega)
    (by simpa only [MachineState.getReg_setPC] using readyHeap) (3 + fuel) true
  rw [show 35 + fuel = 8 + (24 + (3 + fuel)) by omega,
    contiguous_salt_execute _ saltFetched _ rfl physicalSalt destinationValid,
    contiguous_salt_ready state messageBase link, leafRun]
  rw [contiguous_heap_pc_bind (cursorLeafFrame ready messageBase) cursor 4488 4584
    (fun finished => do
      let result ← execute (submission.image .commit) (3 + fuel) finished true
      return result.charge 80 8)]
  rw [fused_leaf_reference_bind ready
    cursor (readySource.trans source) readyChain
    (by
      change (ready.getReg .x8).toNat - 32 = cursor
      rw [readySource]) messageBase 4584
    (fun finished => do
      let result ← execute (submission.image .commit) (3 + fuel) finished true
      return result.charge 80 8)]
  simp only [commitPositionRun, commitLeafReadyState, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have leafHeap : leaf.getReg .x23 = state.getReg .x23 :=
    ((commit_leaf_loop_registers ready 8 leaf reached).2 .x23 (by decide)).trans
      (commit_position_register state .x23 (by decide) (by decide))
  have leafEnd : leaf.getReg .x22 = state.getReg .x22 :=
    (outer_leaf_end_preserved ready leaf 8 reached).trans
      (commit_position_register state .x22 (by decide) (by decide))
  have branch : BitVec.ult (leaf.getReg .x23 + 32) (leaf.getReg .x22) =
      decide (0 < remaining) := by
    rw [leafHeap, leafEnd]
    exact outer_heap_latch _ _ remaining window
  rw [contiguous_latch_execute _ latchFetched (cursorNormalize leaf messageBase 4584) rfl,
    contiguous_latch_frame, branch]
  rw [cursor_next_frame_pc]
  by_cases empty : remaining = 0 <;>
    simp [empty, Nat.pos_of_ne_zero, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
