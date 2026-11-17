import CommitGolfCandidate.CursorSaltExecution
import CommitGolfCandidate.CursorOuterFrame
import CommitGolfCandidate.FusedLatch

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem fused_position (saltFetched : CursorSaltFetched (submission.image .commit))
    (prefixFetched : CursorPrefixFetched (submission.image .commit))
    (tailFetched : FusedTailFetched (submission.image .commit))
    (latchFetched : FusedLatchFetched (submission.image .commit))
    (state : MachineState) (messageBase : Word) (pc : state.pc = 4280)
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
    execute (submission.image .commit) (36 + fuel) (cursorLeafFrame state messageBase) true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel
            (cursorNormalize finished messageBase (if remaining = 0 then 4564 else 4280)) true
          return result.charge 92 8) := by
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
      accessValid ((cursorLeafFrame state messageBase).getReg .x10 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
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
      accessValid ((cursorLeafFrame state messageBase).getReg .x18 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [cursor_frame_register state messageBase .x18 (by decide)]
    exact saltValid
  have physicalPC : (cursorLeafFrame state messageBase).pc = 4280 := pc
  have copyPC : (cursorLeafFrame (commitCopyState state 46) messageBase).pc = 4312 := by
    rw [cursor_frame_pc, commit_copy_pc, pc]; rfl
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
  have readyLink : (cursorLeafFrame ready messageBase).getReg .x1 = 4316 := by
    rw [cursor_frame_register ready messageBase .x1 (by decide)]
    rfl
  have leafRun := fused_leaf_blocks (submission.image .commit) prefixFetched tailFetched
    (cursorLeafFrame ready messageBase) cursor (by rfl)
    (by rw [cursor_frame_pointer]; exact readyChain) readyOracle
    (by dsimp [cursor]; omega) (by dsimp [cursor]; omega) readyHeap (3 + fuel) true
  dsimp only [ready, commitPositionState] at leafRun
  rw [show 36 + fuel = 8 + (1 + (24 + (3 + fuel))) by omega,
    cursor_salt_execute _ saltFetched _ physicalPC physicalSalt destinationValid,
    cursor_salt_copy_frame, commit_leaf_call _ copyPC, cursor_call_frame, leafRun]
  rw [fused_leaf_reference_bind (commitLeafCallState (commitCopyState state 46))
    cursor (readySource.trans source) readyChain
    (by
      change (ready.getReg .x8).toNat - 32 = cursor
      rw [readySource]) messageBase 4552
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
  rw [fused_latch_execute _ latchFetched (cursorNormalize leaf messageBase 4552) rfl,
    fused_latch_frame, branch]
  rw [cursor_next_frame_pc]
  by_cases empty : remaining = 0 <;>
    simp [empty, Nat.pos_of_ne_zero, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
