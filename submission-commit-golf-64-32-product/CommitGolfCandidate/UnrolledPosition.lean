import CommitGolfCandidate.UnrolledBlocks

/-! One unrolled leaf: the salt copy and eight compression blocks at fixed
offsets, with no pointer advance and no branch. The live frame falls one more
leaf behind the reference, which advances its salt and heap pointers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem unrolled_lag (value : Word) (step slot : Nat) :
    value + BitVec.ofNat 64 step - BitVec.ofNat 64 (step * (slot + 1)) =
      value - BitVec.ofNat 64 (step * slot) := by
  rw [show step * (slot + 1) = step * slot + step by ring, BitVec.ofNat_add]
  generalize BitVec.ofNat 64 step = b
  generalize BitVec.ofNat 64 (step * slot) = c
  rw [← BitVec.sub_sub, ← BitVec.sub_add_comm, BitVec.add_sub_cancel]

/-- The reference pointer advance is exactly one more leaf of lag. -/
theorem unrolled_next_frame (state : MachineState) (messageBase returnPC pc : Word) (slot : Nat) :
    unrolledShift (slot + 1)
        (cursorNormalize (commitPositionNextState (state.setPC returnPC)) messageBase pc) =
      unrolledShift slot (cursorNormalize state messageBase pc) := by
  cases state
  dsimp [unrolledShift, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    commitPositionNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> simp [unrolled_lag]

theorem unrolled_salt_ready (state : MachineState) (messageBase pc next : Word)
    (link : state.getReg .x1 = 4316) :
    (cursorSaltCopyState (cursorNormalize state messageBase pc)).setPC next =
      (cursorLeafFrame (commitPositionState state) messageBase).setPC next := by
  change (cursorSaltCopyState (cursorLeafFrame (state.setPC pc) messageBase)).setPC next = _
  rw [cursor_salt_copy_frame, contiguous_copy_pc]
  have copiedLink : (commitCopyState state 46).getReg .x1 = 4316 := by
    rw [commit_copy_register state 46 .x1 (by decide)]
    exact link
  have sameLink : (commitCopyState state 46).setReg .x1 4316 = commitCopyState state 46 := by
    rw [← copiedLink]
    generalize commitCopyState state 46 = copied
    cases copied
    dsimp [MachineState.setReg, MachineState.getReg]
    congr 1
    funext reg
    cases reg <;> rfl
  simp only [commitPositionState, commitLeafCallState, sameLink]
  rfl

/-- One unrolled leaf: 31 instructions, 87 cycles and eight queries. The
reference position run advances salt and heap pointers that the live frame keeps. -/
theorem unrolled_position (image : Image) (slot : Nat) (small : slot < 64) (start : Word)
    (saltFetched : UnrolledSaltFetched image slot start)
    (blocksFetched : UnrolledBlocksFetched image slot (start + 28))
    (state : MachineState) (messageBase : Word)
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
    (fuel : Nat) :
    execute image (31 + fuel) (unrolledShift slot (cursorNormalize state messageBase start)) true =
      (do let finished ← commitPositionRun state
          let result ← execute image fuel
            (unrolledShift (slot + 1) (cursorNormalize finished messageBase (start + 124))) true
          return result.charge 87 8) := by
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
      accessValid ((cursorNormalize state messageBase start).getReg .x10 +
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
  have physicalSalt : ∀ word : Fin 3,
      accessValid ((cursorNormalize state messageBase start).getReg .x18 +
        BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    change ∀ word : Fin 3, accessValid ((cursorLeafFrame state messageBase).getReg .x18 +
      BitVec.ofNat 64 (8 * word.val)) 8 = true
    rw [cursor_frame_register state messageBase .x18 (by decide)]
    exact fun word => saltValid ⟨word.val, by omega⟩
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
  have leafRun := unrolled_leaf_blocks image slot (by omega) (start + 28) blocksFetched
    ((cursorLeafFrame ready messageBase).setPC (start + 28)) cursor rfl
    (by rw [MachineState.getReg_setPC, cursor_frame_pointer]; exact readyChain)
    (by simpa only [StreamingOracleReady, MachineState.getReg_setPC] using readyOracle)
    (by dsimp [cursor]; omega) (by dsimp [cursor]; omega)
    (by simpa only [MachineState.getReg_setPC] using readyHeap) fuel true
  rw [show 31 + fuel = 7 + (24 + fuel) by omega,
    unrolled_salt_execute image slot small start saltFetched _ rfl physicalSalt destinationValid,
    nonce_salt_virtual,
    show nonceVirtualSaltState (cursorNormalize state messageBase start) =
      cursorSaltCopyState (cursorNormalize state messageBase start) from rfl,
    show (cursorNormalize state messageBase start).pc + 28 = start + 28 from rfl,
    unrolled_salt_ready state messageBase start (start + 28) link, leafRun]
  rw [contiguous_heap_pc_bind (cursorLeafFrame ready messageBase) cursor (start + 28)
    (start + 28 + 96)
    (fun finished => do
      let result ← execute image fuel (unrolledShift slot finished) true
      return result.charge 80 8)]
  rw [fused_leaf_reference_bind ready
    cursor (readySource.trans source) readyChain
    (by
      change (ready.getReg .x8).toNat - 32 = cursor
      rw [readySource]) messageBase (start + 28 + 96)
    (fun finished => do
      let result ← execute image fuel (unrolledShift slot finished) true
      return result.charge 80 8)]
  simp only [commitPositionRun, commitLeafReadyState, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have endPC : start + 28 + 96 = start + 124 := by
    rw [BitVec.add_assoc]
    rfl
  rw [endPC, unrolled_next_frame leaf messageBase 4348 (start + 124) slot]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
