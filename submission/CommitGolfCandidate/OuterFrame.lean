import CommitGolfCandidate.Commit
import CommitGolfCandidate.PointerStart
/-! Counter and program-counter frames for the heap-end latch. The x20 frame
adapts published e016 OuterHelpers to the direct-to-heap streaming operations.
Physical execution and access checks are established in HeapLatch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
theorem outer_write {bits : Nat} (state : MachineState) (address : Word)
    (answer : BitVec bits) (value : Word) :
    writeBits (state.setReg .x20 value) address answer =
      (writeBits state address answer).setReg .x20 value := by
  have byte_reg (s : MachineState) (a : Word) (b : BitVec 8) :
      (s.setReg .x20 value).setByte a b = (s.setByte a b).setReg .x20 value := by
    cases s; rfl
  have fold (indices : List Nat) (current : MachineState) :
      indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) (current.setReg .x20 value) =
      (indices.foldl (fun s i => s.setByte (address + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i)))) current).setReg .x20 value := by
    induction indices generalizing current with
    | nil => rfl
    | cons i rest ih =>
      simpa only [List.foldl_cons,byte_reg] using ih
        (current.setByte (address + BitVec.ofNat 64 i)
          (BitVec.ofNat 8 (answer.toNat / 2 ^ (8 * i))))
  unfold writeBits
  rw [fold]
  rfl


theorem outer_streaming_args (state : MachineState) (cursor : Nat) (value : Word) :
    streamingArgsState (state.setReg .x20 value) cursor =
      (streamingArgsState state cursor).setReg .x20 value := by
  cases state
  dsimp [streamingArgsState, MachineState.setReg, MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_streaming_reply (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) (value : Word) :
    streamingReplyState (state.setReg .x20 value) cursor answer =
      (streamingReplyState state cursor answer).setReg .x20 value := by
  unfold streamingReplyState
  rw [outer_streaming_args, outer_write]

theorem outer_streaming_bind {α : Type} (state : MachineState) (cursor count : Nat)
    (value : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← streamingMachineBlocks (state.setReg .x20 value) cursor count
        continuation finished) =
      (do let finished ← streamingMachineBlocks state cursor count
          continuation (finished.setReg .x20 value)) := by
  induction count generalizing state cursor with
  | zero => rfl
  | succ count ih =>
    have inputEq : readBuffer (state.setReg .x20 value) cursor 64 = readBuffer state cursor 64 := rfl
    simp only [streamingMachineBlocks, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) : OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [outer_streaming_reply]
    exact ih _ _

theorem outer_heap_args (state : MachineState) (cursor : Nat) (value : Word) :
    heapStreamingArgsState (state.setReg .x20 value) cursor =
      (heapStreamingArgsState state cursor).setReg .x20 value := by
  cases state
  dsimp [heapStreamingArgsState, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_heap_reply (state : MachineState) (cursor : Nat)
    (answer : BitVec 256) (value : Word) :
    heapStreamingReplyState (state.setReg .x20 value) cursor answer =
      (heapStreamingReplyState state cursor answer).setReg .x20 value := by
  unfold heapStreamingReplyState
  rw [outer_heap_args]
  change writeBits ((heapStreamingArgsState state cursor).setReg .x20 value)
    (state.getReg .x23) answer = _
  rw [outer_write]
theorem outer_heap_bind {α : Type} (state : MachineState) (cursor count : Nat)
    (value : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← heapStreamingMachineBlocks (state.setReg .x20 value) cursor count
        continuation finished) =
      (do let finished ← heapStreamingMachineBlocks state cursor count
          continuation (finished.setReg .x20 value)) := by
  cases count with
  | zero => rfl
  | succ count =>
    simp only [heapStreamingMachineBlocks, bind_assoc, pure_bind]
    rw [outer_streaming_bind]
    apply congrArg (fun tail => streamingMachineBlocks state cursor count >>= tail)
    funext body
    have inputEq : readBuffer (body.setReg .x20 value) (cursor + 32 * count) 64 =
        readBuffer body (cursor + 32 * count) 64 := rfl
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer body (cursor + 32 * count) 64)))) : OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    rw [outer_heap_reply]

theorem outer_finish_frame (state : MachineState) (count : Nat) (value : Word) :
    commitLeafFinishState (state.setReg .x20 value) count =
      (commitLeafFinishState state count).setReg .x20 value := by
  cases state
  dsimp [commitLeafFinishState, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_leaf_bind {α : Type} (state : MachineState) (count : Nat)
    (value : Word) (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitLeafLoop (state.setReg .x20 value) count
        continuation finished) =
      (do let finished ← commitLeafLoop state count
          continuation (finished.setReg .x20 value)) := by
  simp only [commitLeafLoop, bind_assoc, pure_bind]
  change (do let finished ← heapStreamingMachineBlocks (state.setReg .x20 value)
               ((state.getReg .x8).toNat - 32) count
             continuation (commitLeafFinishState finished count)) = _
  rw [outer_heap_bind]
  apply congrArg (fun tail =>
    heapStreamingMachineBlocks state ((state.getReg .x8).toNat - 32) count >>= tail)
  funext finished
  rw [outer_finish_frame]

/- The salt-copy and outer-counter normalization below adapt the published
 e016 OuterHelpers proof, with the direct-heap leaf replacing its scratch loop. -/
private def outerCopyOps (source destination : Reg) (offset : Nat) : List Instr :=
  [.LD .x6 source (BitVec.ofNat 12 offset), .SD destination .x6 0,
   .LD .x6 source (BitVec.ofNat 12 (offset+8)), .SD destination .x6 8,
   .LD .x6 source (BitVec.ofNat 12 (offset+16)), .SD destination .x6 16,
   .LD .x6 source (BitVec.ofNat 12 (offset+24)), .SD destination .x6 24]

set_option maxHeartbeats 2000000 in
theorem outer_salt_copy (state : MachineState) (value : Word) :
    commitCopyState (state.setReg .x20 value) 46 =
      (commitCopyState state 46).setReg .x20 value := by
  change (outerCopyOps .x18 .x21 0).foldl execInstrBr (state.setReg .x20 value) =
    ((outerCopyOps .x18 .x21 0).foldl execInstrBr state).setReg .x20 value
  cases state
  dsimp [outerCopyOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_position_state (state : MachineState) (value : Word) :
    commitPositionState (state.setReg .x20 value) =
      (commitPositionState state).setReg .x20 value := by
  unfold commitPositionState
  rw [outer_salt_copy]
  unfold commitLeafCallState
  generalize commitCopyState state 46=middle
  cases middle
  dsimp [MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_ready (state : MachineState) (value : Word) :
    commitLeafReadyState (state.setReg .x20 value) =
      (commitLeafReadyState state).setReg .x20 value := by
  rfl

def outerNormalize (state : MachineState) (pc : Word) : MachineState :=
  (state.setReg .x20 0).setPC pc

theorem outer_next_erase (state : MachineState) (value pc : Word) :
    outerNormalize (commitPositionNextState (state.setReg .x20 value)) pc =
      outerNormalize (commitPositionNextState state) pc := by
  cases state
  dsimp [outerNormalize,commitPositionNextState,MachineState.getReg,
    MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem outer_reg_pc (state : MachineState) (value pc : Word) :
    (state.setReg .x20 value).setPC pc=(state.setPC pc).setReg .x20 value := by
  cases state
  rfl

theorem outer_position_bind {α : Type} (state : MachineState) (value pc : Word)
    (continuation : MachineState → OracleComp World α) :
    (do let finished ← commitPositionRun (state.setReg .x20 value)
        continuation (outerNormalize finished pc)) =
      (do let finished ← commitPositionRun state
          continuation (outerNormalize finished pc)) := by
  simp only [commitPositionRun,bind_assoc,pure_bind]
  rw [outer_position_state,outer_ready,outer_leaf_bind]
  apply congrArg (fun tail => commitLeafLoop
    (commitLeafReadyState (commitPositionState state)) 8 >>= tail)
  funext leaf
  rw [outer_reg_pc,outer_next_erase]


/-- Natural end-pointer invariant makes the actual unsigned latch equivalent
 to the logical residual count, without relying on the physical x20 counter. -/
theorem outer_heap_latch (heap ending : Word) (remaining : Nat)
    (window : heap.toNat + 32 * (remaining + 1) = ending.toNat) :
    BitVec.ult (heap + 32) ending = decide (0 < remaining) := by
  have noWrap : heap.toNat + 32 < 2^64 := by
    have endBound := ending.isLt
    omega
  have advanced : (heap + 32).toNat = heap.toNat + 32 := by
    rw [BitVec.toNat_add]
    change (heap.toNat + 32) % 2^64 = _
    exact Nat.mod_eq_of_lt noWrap
  have branch : heap.toNat + 32 < ending.toNat ↔ 0 < remaining := by omega
  simp only [BitVec.ult,advanced,branch]

/-- Streaming and the final heap reply preserve the recorded end pointer. -/
theorem outer_leaf_end_preserved (state finished : MachineState) (count : Nat)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x22 = state.getReg .x22 := by
  exact (commit_leaf_loop_registers state count finished reachable).2 .x22 (by decide)


set_option maxHeartbeats 2000000 in
theorem outer_salt_copy_pc (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 46 =
      (commitCopyState state 46).setPC (pc+32) := by
  change (outerCopyOps .x18 .x21 0).foldl execInstrBr (state.setPC pc) =
    ((outerCopyOps .x18 .x21 0).foldl execInstrBr state).setPC (pc+32)
  cases state
  dsimp [outerCopyOps,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.getMem,MachineState.setMem,MachineState.setPC]
  congr 1
  simp [BitVec.add_assoc]

theorem outer_position_state_pc (state : MachineState) (pc : Word) :
    commitPositionState (state.setPC pc)=commitPositionState state := by
  unfold commitPositionState
  rw [outer_salt_copy_pc]
  unfold commitLeafCallState
  generalize commitCopyState state 46=middle
  cases middle
  rfl

theorem outer_position_run_pc (state : MachineState) (pc : Word) :
    commitPositionRun (state.setPC pc)=commitPositionRun state := by
  unfold commitPositionRun
  rw [outer_position_state_pc]


private def outerParentPrefix (state : MachineState) : MachineState :=
  ([.ADDI .x20 .x19 4095, .SLLI .x6 .x20 6,
    .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5] : List Instr).foldl execInstrBr state

private def outerParentBranch (state : MachineState) : MachineState :=
  (outerParentPrefix state).setPC (if state.getReg .x19 - 1 = 0 then 4412 else 4384)

set_option maxHeartbeats 2000000 in
theorem outer_parent_prefix_erase (state : MachineState) (value : Word) :
    outerParentPrefix (state.setReg .x20 value) = outerParentPrefix state := by
  cases state
  dsimp [outerParentPrefix,List.foldl,execInstrBr,signExtend12,MachineState.getReg,
    MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

/-- Parent setup overwrites the virtual outer counter before using it. -/
theorem outer_parent_counter_erase (state : MachineState) (value : Word) :
    commitParentsStartState (state.setReg .x20 value) = commitParentsStartState state := by
  have branch : outerParentBranch (state.setReg .x20 value) =
      outerParentBranch state := by
    unfold outerParentBranch
    change (outerParentPrefix (state.setReg .x20 value)).setPC
      (if state.getReg .x19 - 1 = 0 then 4412 else 4384) = _
    rw [outer_parent_prefix_erase]
  change (if state.getReg .x19 - 1 = 0 then outerParentBranch (state.setReg .x20 value)
    else execInstrBr (outerParentBranch (state.setReg .x20 value)) (.ADD .x12 .x9 .x7)) =
    (if state.getReg .x19 - 1 = 0 then outerParentBranch state
    else execInstrBr (outerParentBranch state) (.ADD .x12 .x9 .x7))
  rw [branch]


/-- The retained reference outer position preserves the recorded heap end. -/
theorem outer_position_end_preserved (state finished : MachineState)
    (reachable : finished ∈ support (commitPositionRun state)) :
    finished.getReg .x22 = state.getReg .x22 := by
  simp only [commitPositionRun,mem_support_bind_iff,support_pure,
    Set.mem_singleton_iff] at reachable
  obtain ⟨leaf,reached,rfl⟩ := reachable
  have leafEnd := outer_leaf_end_preserved
    (commitLeafReadyState (commitPositionState state)) leaf 8 reached
  have readyEnd : (commitLeafReadyState (commitPositionState state)).getReg .x22 =
      state.getReg .x22 := by
    rw [commit_leaf_ready_register]
    exact commit_position_register state .x22 (by decide) (by decide)
  have outer : (commitPositionNextState (leaf.setPC 4348)).getReg .x22 =
      leaf.getReg .x22 := rfl
  exact outer.trans (leafEnd.trans readyEnd)


theorem outer_normalize_idempotent (state : MachineState) (first second : Word) :
    outerNormalize (outerNormalize state first) second =
      outerNormalize state second := by
  cases state
  dsimp [outerNormalize,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

def outerLatchInstructions : List Instr :=
  [.ADDI .x18 .x18 32, .ADDI .x23 .x23 32, .BLTU .x23 .x22 8116]

def outerLatchPrefix (state : MachineState) (count : Nat) : MachineState :=
  (outerLatchInstructions.take count).foldl execInstrBr state

def outerPhysicalNextState (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18+32)).setReg .x23 (state.getReg .x23+32)).setPC
    (if BitVec.ult (state.getReg .x23+32) (state.getReg .x22) then 4280 else 4360)

theorem outer_latch_state (state : MachineState) (pc : state.pc=4348) :
    outerLatchPrefix state 3 = outerPhysicalNextState state := by
  simp [outerLatchPrefix,outerLatchInstructions,List.foldl,execInstrBr,
    signExtend12,signExtend13,MachineState.getReg,MachineState.setReg,
    MachineState.setPC,outerPhysicalNextState,pc]
  split <;> simp_all

/-- This bridges the real ordinary-step interpreter with exact three-cycle
 latch execution, CONDITIONAL on fetching all three proposed bytes. HeapLatch discharges every fetch
 premise against the assembled candidate bytes. -/
theorem outer_latch_execute (image : Image) (state : MachineState) (fuel : Nat)
    (pc : state.pc=4348)
    (fetched : ∀ i < 3, fetch image (outerLatchPrefix state i) =
      some (.base ((outerLatchInstructions[i]?).getD .EBREAK))) :
    execute image (3+fuel) state true =
      (do let result ← execute image fuel (outerPhysicalNextState state) true
          return result.charge 3 0) := by
  have trace : execute image (3+fuel) state true =
      (do let result ← execute image fuel (outerLatchPrefix state 3) true
          return result.charge 3 0) := by
    apply execute_unit_steps (states:=outerLatchPrefix state)
    intro i hi
    refine ⟨.base ((outerLatchInstructions[i]?).getD .EBREAK),fetched i hi,?_,?_⟩
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  rw [outer_latch_state state pc] at trace
  exact trace


/-- The proposed physical latch advances the same live pointers as the retained
 reference latch, while erasing its virtual counter and replacing its PC. -/
theorem outer_latch_normalized (state : MachineState) :
    outerPhysicalNextState (outerNormalize state 4348) =
      outerNormalize (commitPositionNextState state)
        (if BitVec.ult (state.getReg .x23+32) (state.getReg .x22) then 4280 else 4360) := by
  cases state
  dsimp [outerPhysicalNextState,outerNormalize,commitPositionNextState,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl


/-- Exact natural interval progress for the retained reference leaf distribution. -/
theorem outer_heap_progress_next (state finished : MachineState) (remaining : Nat)
    (window : (state.getReg .x23).toNat + 32*(remaining+1) =
      (state.getReg .x22).toNat)
    (reachable : finished ∈ support (commitPositionRun state)) :
    (finished.getReg .x23).toNat + 32*remaining = (finished.getReg .x22).toNat := by
  have advanced := (commit_position_registers state finished reachable).2.2.1
  rw [advanced,outer_position_end_preserved state finished reachable]
  have noWrap : (state.getReg .x23).toNat+32 < 2^64 := by
    have endBound := (state.getReg .x22).isLt
    omega
  rw [BitVec.toNat_add]
  change ((state.getReg .x23).toNat+32)%2^64 + 32*remaining = _
  rw [Nat.mod_eq_of_lt noWrap]
  omega

/-- The once-only fall-through NOP restores the retained parent entry PC.
 Parent setup then erases the physical/virtual outer counter difference. -/
theorem outer_exit_parent_frame (state : MachineState) :
    commitParentsStartState (execInstrBr (outerNormalize state 4360) (.ADDI .x0 .x0 0)) =
      commitParentsStartState (state.setPC 4364) := by
  have exit : execInstrBr (outerNormalize state 4360) (.ADDI .x0 .x0 0) =
      (state.setPC 4364).setReg .x20 0 := by
    cases state
    dsimp [outerNormalize,execInstrBr,MachineState.setPC,MachineState.setReg]
  rw [exit,outer_parent_counter_erase]

end CommitGolfCandidate
