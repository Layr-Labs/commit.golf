import CommitGolfCandidate.ContiguousLoop
import CommitGolfCandidate.ContiguousPreparation

/-! A relocatable copy of the contiguous leaf body. Each body has seven salt
instructions, seven prefix triples, the heap query triple and two pointer
increments, with no branch. Fetch premises are relative to a symbolic base. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem unroll_pc_add (x y z : Nat) (h : x + y = z) :
    BitVec.ofNat 64 x + BitVec.ofNat 64 y = BitVec.ofNat 64 z := by
  subst h
  exact (BitVec.ofNat_add x y).symm

theorem unroll_pc_four (x : Nat) : BitVec.ofNat 64 x + 4 = BitVec.ofNat 64 (x + 4) :=
  (BitVec.ofNat_add x 4).symm

def UnrollSaltFetched (image : Image) (B : Nat) : Prop :=
  ∀ (state : MachineState) (i : Nat), i<7 → state.pc=BitVec.ofNat 64 (B+4*i) →
    fetch image state=some (.base ((nonceSaltInstructions[i]?).getD .EBREAK))

def UnrollPrefixFetched (image : Image) (B : Nat) : Prop :=
  ∀ (state : MachineState) (block : Nat), block < 7 →
    (state.pc = BitVec.ofNat 64 (B + 28 + 12 * block) →
      fetch image state = some (.base (.ADDI .x12 .x10 32))) ∧
    (state.pc = BitVec.ofNat 64 (B + 32 + 12 * block) →
      fetch image state = some (.base .ECALL)) ∧
    (state.pc = BitVec.ofNat 64 (B + 36 + 12 * block) →
      fetch image state = some (.base (.ADDI .x10 .x10 32)))

def UnrollTailFetched (image : Image) (B : Nat) : Prop :=
  ∀ state : MachineState,
    (state.pc = BitVec.ofNat 64 (B + 112) → fetch image state = some (.base (.ADDI .x12 .x23 0))) ∧
    (state.pc = BitVec.ofNat 64 (B + 116) → fetch image state = some (.base .ECALL)) ∧
    (state.pc = BitVec.ofNat 64 (B + 120) → fetch image state = some (.base (.ADDI .x10 .x10 32))) ∧
    (state.pc = BitVec.ofNat 64 (B + 124) → fetch image state = some (.base (.ADDI .x18 .x18 24))) ∧
    (state.pc = BitVec.ofNat 64 (B + 128) → fetch image state = some (.base (.ADDI .x23 .x23 32)))

structure UnrollBodyFetched (image : Image) (B : Nat) : Prop where
  salt : UnrollSaltFetched image B
  pre : UnrollPrefixFetched image B
  tail : UnrollTailFetched image B

theorem unroll_salt_prefix_pc (state : MachineState) (i : Nat) (bounded : i < 7) :
    (nonceSaltPrefix state i).pc = state.pc + BitVec.ofNat 64 (4*i) := by
  interval_cases i <;>
    simp [nonceSaltPrefix, nonceSaltInstructions, execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem unroll_salt_execute (image : Image) (B : Nat) (fetched : UnrollSaltFetched image B)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 B)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute image (7 + fuel) state true =
      (do let result ← execute image fuel ((cursorSaltCopyState state).setPC (BitVec.ofNat 64 (B + 28))) true
          return result.charge 7 0) := by
  have run : execute image (7 + fuel) state true =
      (do let result ← execute image fuel (nonceSaltPrefix state 7) true
          return result.charge 7 0) := by
    apply execute_unit_steps (states := nonceSaltPrefix state)
    intro i hi
    refine ⟨.base ((nonceSaltInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply fetched _ i hi
      rw [unroll_salt_prefix_pc state i hi, pc]
      exact unroll_pc_add _ _ _ rfl
    · have source := nonce_salt_prefix_register state i (by omega) .x18 (by decide)
      have destination := nonce_salt_prefix_register state i (by omega) .x10 (by decide)
      have s0 := sourceValid ⟨0, by decide⟩
      have s1 := sourceValid ⟨1, by decide⟩
      have s2 := sourceValid ⟨2, by decide⟩
      have d0 := destinationValid ⟨0, by decide⟩
      have d1 := destinationValid ⟨1, by decide⟩
      have d2 := destinationValid ⟨2, by decide⟩
      have d3 := destinationValid ⟨3, by decide⟩
      have valid : memoryArgumentsValid (nonceSaltPrefix state i)
          ((nonceSaltInstructions[i]?).getD .EBREAK) = true := by
        interval_cases i <;>
          simp only [nonceSaltInstructions, List.getElem?_cons_zero,
            List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
            memAccess, source, destination, signExtend12] <;>
          first | exact s0 | exact s1 | exact s2 |
            exact d0 | exact d1 | exact d2 | exact d3
      interval_cases i <;>
        simp only [nonceSaltInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
        simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
    · interval_cases i <;> rfl
  have final : nonceSaltPrefix state 7 = (nonceVirtualSaltState state).setPC (BitVec.ofNat 64 (B + 28)) := by
    change nonceSaltState state = _
    rw [nonce_salt_virtual, pc]
    congr 1
    exact (BitVec.ofNat_add B 28).symm
  rw [run, final, show nonceVirtualSaltState state = cursorSaltCopyState state from rfl]

theorem unroll_prefix_block (image : Image) (B : Nat) (fetched : UnrollPrefixFetched image B)
    (state : MachineState) (block cursor : Nat) (blockBound : block < 7)
    (pc : state.pc = BitVec.ofNat 64 (B + 28 + 12 * block))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (cursorNextState state false answer) allowCoins
          return result.charge 10 1) := by
  apply cursor_machine_block image state cursor false pointer ready aligned bounded heapValid
  · exact (fetched state block blockBound).1 pc
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      cursorOutputState, signExtend12]
  · apply (fetched (cursorOutputState state false) block blockBound).2.1
    change state.pc + BitVec.ofNat 64 4 = _
    rw [pc]
    exact unroll_pc_add _ _ _ (by omega)
  · intro answer
    apply (fetched (cursorReplyState state false answer) block blockBound).2.2
    change state.pc + BitVec.ofNat 64 4 + BitVec.ofNat 64 4 = _
    rw [pc, unroll_pc_add _ _ _ rfl]
    exact unroll_pc_add _ _ _ (by omega)
  · intro answer
    have input : (cursorReplyState state false answer).getReg .x10 =
        state.getReg .x10 := by
      rw [cursorReplyState, writeBits_register]
      rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      input]
    change some (((cursorReplyState state false answer).setReg .x10
      (state.getReg .x10 + signExtend12 32)).setPC (state.pc + 4 + 4 + 4)) =
      some (cursorNextState state false answer)
    simp [signExtend12, cursorNextState, BitVec.add_assoc]

theorem unroll_prefix_execute (image : Image) (B : Nat) (fetched : UnrollPrefixFetched image B)
    (state : MachineState) (first cursor count : Nat)
    (blocks : first + count ≤ 7)
    (pc : state.pc = BitVec.ofNat 64 (B + 28 + 12 * first))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 32 * count + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 * count + fuel) state allowCoins =
      (do let finished ← cursorPrefix state cursor count
          let result ← execute image fuel finished allowCoins
          return result.charge (10 * count) count) := by
  induction count generalizing state first cursor with
  | zero => simp [cursorPrefix, Execution.charge]
  | succ count ih =>
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      unroll_prefix_block image B fetched state first cursor (by omega) pc pointer
        ready aligned (by omega) heapValid]
    simp only [cursorPrefix, bind_assoc]
    apply congrArg (fun tail =>
      (liftM (World.query (.inr (.inl (readBuffer state cursor 64)))) :
        OracleComp World (BitVec 256)) >>= tail)
    funext answer
    change BitVec 256 at answer
    have nextPC : (cursorNextState state false answer).pc =
        BitVec.ofNat 64 (B + 28 + 12 * (first + 1)) := by
      rw [cursor_next_pc, pc]
      change BitVec.ofNat 64 (B + 28 + 12 * first) + BitVec.ofNat 64 12 = _
      exact unroll_pc_add _ _ _ (by omega)
    have nextPointer : (cursorNextState state false answer).getReg .x10 =
        BitVec.ofNat 64 (cursor + 32) := by
      rw [cursor_next_pointer, pointer]
      exact (BitVec.ofNat_add cursor 32).symm
    have nextHeap : rangeValid ((cursorNextState state false answer).getReg .x23) 32 = true ∧
        ((cursorNextState state false answer).getReg .x23).toNat % 8 = 0 := by
      rw [cursor_next_register state false answer .x23 (by decide)]
      exact heapValid
    rw [ih (cursorNextState state false answer) (first + 1) (cursor + 32)
      (by omega) nextPC nextPointer (cursor_next_ready state false answer ready)
      (by omega) (by omega) nextHeap]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem unroll_heap_block (image : Image) (B : Nat) (fetched : UnrollTailFetched image B)
    (state : MachineState) (cursor : Nat) (pc : state.pc = BitVec.ofNat 64 (B + 112))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 64 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state cursor 64)))
          let result ← execute image fuel (cursorNextState state true answer) allowCoins
          return result.charge 10 1) := by
  apply cursor_machine_block image state cursor true pointer ready aligned bounded heapValid
  · exact (fetched state).1 pc
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      cursorOutputState, signExtend12]
  · apply (fetched (cursorOutputState state true)).2.1
    change state.pc + BitVec.ofNat 64 4 = _
    rw [pc]
    exact unroll_pc_add _ _ _ rfl
  · intro answer
    apply (fetched (cursorReplyState state true answer)).2.2.1
    change state.pc + BitVec.ofNat 64 4 + BitVec.ofNat 64 4 = _
    rw [pc, unroll_pc_add _ _ _ rfl]
    exact unroll_pc_add _ _ _ rfl
  · intro answer
    have input : (cursorReplyState state true answer).getReg .x10 =
        state.getReg .x10 := by
      rw [cursorReplyState, writeBits_register]
      rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      input]
    change some (((cursorReplyState state true answer).setReg .x10
      (state.getReg .x10 + signExtend12 32)).setPC (state.pc + 4 + 4 + 4)) =
      some (cursorNextState state true answer)
    simp [signExtend12, cursorNextState, BitVec.add_assoc]

theorem unroll_leaf_blocks (image : Image) (B : Nat)
    (prefixFetched : UnrollPrefixFetched image B) (tailFetched : UnrollTailFetched image B)
    (state : MachineState) (cursor : Nat) (pc : state.pc = BitVec.ofNat 64 (B + 28))
    (pointer : state.getReg .x10 = BitVec.ofNat 64 cursor)
    (ready : StreamingOracleReady state) (aligned : cursor % 8 = 0)
    (bounded : cursor + 288 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (24 + fuel) state allowCoins =
      (do let finished ← cursorHeapBlocks state cursor 8
          let result ← execute image fuel (finished.setPC (BitVec.ofNat 64 (B + 124))) allowCoins
          return result.charge 80 8) := by
  rw [show 24 + fuel = 3 * 7 + (3 + fuel) by omega,
    unroll_prefix_execute image B prefixFetched state 0 cursor 7 (by decide)
      (by simpa using pc) pointer ready aligned (by simpa using bounded) heapValid]
  simp only [cursorHeapBlocks, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have lastPC : body.pc = BitVec.ofNat 64 (B + 112) := by
    rw [cursor_prefix_pc state cursor 7 body reached, pc]
    exact unroll_pc_add _ _ _ rfl
  have lastPointer := cursor_prefix_pointer state cursor 7 pointer body reached
  have lastHeap : rangeValid (body.getReg .x23) 32 = true ∧
      (body.getReg .x23).toNat % 8 = 0 := by
    rw [cursor_prefix_register state cursor 7 body reached .x23 (by decide)]
    exact heapValid
  rw [unroll_heap_block image B tailFetched body (cursor + 32 * 7) lastPC lastPointer
    (cursor_prefix_ready state cursor 7 ready body reached) (by omega) (by omega) lastHeap]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  have returnPC : (cursorNextState body true answer).pc = BitVec.ofNat 64 (B + 124) := by
    rw [cursor_next_pc, lastPC]
    exact unroll_pc_add _ _ _ rfl
  rw [← returnPC, hoist_pc_self]
  simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

def unrollLatchState (state : MachineState) (B : Nat) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18 + 24)).setReg .x23
    (state.getReg .x23 + 32)).setPC (BitVec.ofNat 64 (B + 132))

theorem unroll_latch_execute (image : Image) (B : Nat) (fetched : UnrollTailFetched image B)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (B + 124)) (fuel : Nat) :
    execute image (2 + fuel) state true =
      (do let result ← execute image fuel (unrollLatchState state B) true
          return result.charge 2 0) := by
  let first := (state.setReg .x18 (state.getReg .x18 + 24)).setPC (BitVec.ofNat 64 (B + 128))
  have firstStep : ordinaryStep state (.base (.ADDI .x18 .x18 24)) = some first := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr]
    change some ((state.setReg .x18 (state.getReg .x18 + signExtend12 24)).setPC (state.pc + 4)) = _
    rw [pc, unroll_pc_four]
    rfl
  have secondStep : ordinaryStep first (.base (.ADDI .x23 .x23 32)) = some (unrollLatchState state B) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr]
    change some ((first.setReg .x23 (first.getReg .x23 + signExtend12 32)).setPC (BitVec.ofNat 64 (B + 128) + 4)) = _
    rw [unroll_pc_four, show B + 128 + 4 = B + 132 by omega]
    cases state
    rfl
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ ((fetched state).2.2.2.1 pc) firstStep]
  rw [execute_ordinary_step _ _ _ _ _ _ ((fetched first).2.2.2.2 rfl) secondStep]
  simp [pure_bind, Execution.charge, instructionCycles, ← Nat.add_assoc]

theorem unroll_latch_frame (state : MachineState) (messageBase : Word) (B : Nat) (pc : Word) :
    unrollLatchState (cursorNormalize state messageBase pc) B =
      cursorNormalize (commitPositionNextState state) messageBase (BitVec.ofNat 64 (B + 132)) := by
  cases state
  dsimp [unrollLatchState, cursorNormalize, cursorLeafFrame, cursorBaseFrame,
    commitPositionNextState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC]
  congr 1
  funext reg
  cases reg <;> rfl

theorem unroll_salt_ready (state : MachineState) (messageBase : Word) (B : Nat)
    (link : state.getReg .x1 = 4316) :
    (cursorSaltCopyState (cursorNormalize state messageBase (BitVec.ofNat 64 B))).setPC
        (BitVec.ofNat 64 (B + 28)) =
      (cursorLeafFrame (commitPositionState state) messageBase).setPC (BitVec.ofNat 64 (B + 28)) := by
  change (cursorSaltCopyState (cursorLeafFrame (state.setPC (BitVec.ofNat 64 B)) messageBase)).setPC _ = _
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

end CommitGolfCandidate
