import CommitGolfCandidate.DirectHeapExecution

/-! Execution of the emitted commitment streaming leaf. The source base remains
fixed during eight unrolled blocks. The final digest goes to x23; x21 advances
to the consumed final message block for the next salt. Return skips the caller
copy. All bounds and replies are checked by the real interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 200) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .commit).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

private theorem streaming_commit_code : (submission.image .commit).code =
  [ 0x00050413#32, 0x00058d13#32, 0x00060493#32, 0x010009b7#32, 0x0180006f#32, 0x00000013#32,
  0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x40000337#32, 0x0180006f#32,
  0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00648933#32,
  0x20000337#32, 0x0180006f#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32,
  0x00000013#32, 0x00648bb3#32, 0x00200293#32, 0x00090513#32, 0x200005b7#32, 0x0180006f#32,
  0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000073#32,
  0xfe040a93#32, 0x00000013#32, 0x00000013#32, 0x00000a13#32, 0x00000293#32, 0x000a8513#32,
  0x04000593#32, 0x000a8613#32, 0x00000693#32, 0x00000e13#32, 0x00093303#32, 0x006ab023#32,
  0x00893303#32, 0x006ab423#32, 0x01093303#32, 0x006ab823#32, 0x01893303#32, 0x006abc23#32,
  0x090000ef#32, 0x000ab303#32, 0x006bb023#32, 0x008ab303#32, 0x006bb423#32, 0x010ab303#32,
  0x006bb823#32, 0x018ab303#32, 0x006bbc23#32, 0x02090913#32, 0x020b8b93#32, 0x001a0a13#32,
  0xfb3a68e3#32, 0x00000293#32, 0x04000593#32, 0x00000693#32, 0xfff98a13#32, 0x020a0063#32,
  0x006a1313#32, 0x00648533#32, 0x005a1393#32, 0x00748633#32, 0x00000073#32, 0xfffa0a13#32,
  0xfe0a14e3#32, 0x0204b303#32, 0x006d3023#32, 0x0284b303#32, 0x006d3423#32, 0x0304b303#32,
  0x006d3823#32, 0x0384b303#32, 0x006d3c23#32, 0x00100293#32, 0x00000513#32, 0x00000073#32,
  0xfe040513#32, 0x00040613#32, 0x00000073#32, 0x00040513#32, 0x02040613#32, 0x00000073#32,
  0x02040513#32, 0x04040613#32, 0x00000073#32, 0x04040513#32, 0x06040613#32, 0x00000073#32,
  0x06040513#32, 0x08040613#32, 0x00000073#32, 0x08040513#32, 0x0a040613#32, 0x00000073#32,
  0x0a040513#32, 0x0c040613#32, 0x00000073#32, 0x0c040513#32, 0x000b8613#32, 0x00000073#32,
  0x10040413#32, 0xfe040a93#32, 0x02008067#32 ] := by rfl

/-- Only three syscall arguments remain fixed. The two address registers are
computed independently before each compression. -/
abbrev CommitLeafOracleReady := StreamingOracleReady

def commitLeafReadyState (state : MachineState) : MachineState := state.setPC 4456

@[simp] theorem commit_leaf_ready_register (state : MachineState) (reg : Reg) :
    (commitLeafReadyState state).getReg reg = state.getReg reg := rfl

@[simp] theorem commit_leaf_ready_pc (state : MachineState) :
    (commitLeafReadyState state).pc = 4456 := rfl

@[simp] theorem commit_leaf_ready_oracle (state : MachineState)
    (ready : CommitLeafOracleReady state) :
    CommitLeafOracleReady (commitLeafReadyState state) := ready

/-- The final two pointer instructions follow the unrolled block body. -/
def commitLeafFinishState (state : MachineState) (count : Nat) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + BitVec.ofNat 64 (32 * count))).setReg .x21
    (state.getReg .x8 + BitVec.ofNat 64 (32 * count) - 32)).setPC (state.pc + 8)

def commitLeafLoop (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let finished ← heapStreamingMachineBlocks state ((state.getReg .x8).toNat - 32) count
  return commitLeafFinishState finished count

/-- Pointer and PC updates preserve the direct-to-heap memory transform. -/
theorem commit_leaf_loop_memory (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (commitLeafLoop state count)).1.mem =
      (checkEvaluation oracle
        (heapStreamingBlocks state ((state.getReg .x8).toNat - 32) count (state.getReg .x23).toNat)).1.mem := by
  rw [commitLeafLoop, check_evaluation_bind]
  change (commitLeafFinishState
    (checkEvaluation oracle (heapStreamingMachineBlocks state ((state.getReg .x8).toNat - 32) count)).1
    count).mem = _
  change (checkEvaluation oracle
    (heapStreamingMachineBlocks state ((state.getReg .x8).toNat - 32) count)).1.mem = _
  exact (heap_streaming_machine_memory oracle state state _ count rfl).1

/-- The actual leaf's public-query accounting agrees with its memory reference. -/
theorem commit_leaf_loop_queries (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (commitLeafLoop state count)).2 = count := by
  rw [commitLeafLoop, check_evaluation_bind]
  change (checkEvaluation oracle
    (heapStreamingMachineBlocks state ((state.getReg .x8).toNat - 32) count)).2 + 0 = count
  rw [Nat.add_zero, (heap_streaming_machine_memory oracle state state _ count rfl).2,
    heap_streaming_queries]

private theorem commit_streaming_offsets (block : Nat) (bounded : block < 8) :
    signExtend12 (BitVec.ofInt 12 ((32 * block : Int) - 32)) =
      BitVec.ofNat 64 (32 * block) - 32 ∧
    signExtend12 (BitVec.ofNat 12 (32 * block)) = BitVec.ofNat 64 (32 * block) := by
  interval_cases block <;> decide

/-- The caller's checked word accesses imply alignment and a whole-leaf bound.
The first access rules out 64-bit wrapping before the last-word bound is used. -/
theorem commit_leaf_source_range (state : MachineState)
    (valid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true) :
    (state.getReg .x8).toNat % 8 = 0 ∧
      (state.getReg .x8).toNat + 256 ≤ MEMORY_BYTES := by
  have first := valid 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, accessValid, rangeValid,
    Bool.and_eq_true, decide_eq_true_eq] at first
  have noWrap : (state.getReg .x8).toNat + 248 < 2^64 := by
    have bound := first.1
    unfold MEMORY_BYTES at bound
    omega
  have last := valid 31 (by decide)
  simp only [Nat.reduceMul, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq,
    BitVec.toNat_add] at last
  have finalNat : (state.getReg .x8).toNat + (248#64).toNat =
      (state.getReg .x8).toNat + 248 := rfl
  rw [finalNat, Nat.mod_eq_of_lt noWrap] at last
  exact ⟨first.2, by have := last.1; omega⟩

/-- Four checked heap word stores imply the final syscall's 32-byte range and
eight-byte alignment. No stronger 32-byte alignment assumption is needed. -/
theorem commit_leaf_heap_range (state : MachineState)
    (valid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true) :
    rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0 := by
  have first := valid ⟨0, by decide⟩
  simp only [Nat.mul_zero, BitVec.add_zero, accessValid, rangeValid,
    Bool.and_eq_true, decide_eq_true_eq] at first
  have noWrap : (state.getReg .x23).toNat + 24 < 2^64 := by
    have bound := first.1
    unfold MEMORY_BYTES at bound
    omega
  have last := valid ⟨3, by decide⟩
  simp only [Nat.reduceMul, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq,
    BitVec.toNat_add] at last
  have finalNat : (state.getReg .x23).toNat + (24#64).toNat =
      (state.getReg .x23).toNat + 24 := rfl
  rw [finalNat, Nat.mod_eq_of_lt noWrap] at last
  refine ⟨?_, first.2⟩
  simp only [rangeValid, decide_eq_true_eq]
  have := last.1
  omega

/-- The emitted three-word block reads the original message block beside the
previous reply, then overwrites only that consumed block. -/
theorem commit_streaming_block (state : MachineState) (base block : Nat)
    (blockBound : block < 7) (pc : state.pc = BitVec.ofNat 64 (4456 + 12 * block))
    (pointer : state.getReg .x8 = BitVec.ofNat 64 base)
    (ready : CommitLeafOracleReady state) (aligned : base % 8 = 0)
    (above : 32 ≤ base) (bounded : base + 256 ≤ MEMORY_BYTES)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state (base - 32 + 32 * block) 64)))
          let result ← execute (submission.image .commit) fuel
            (streamingReplyState state (base - 32 + 32 * block) answer) allowCoins
          return result.charge 10 1) := by
  let cursor := base - 32 + 32 * block
  have offsets := commit_streaming_offsets block (by omega)
  have source : state.getReg .x8 +
      signExtend12 (BitVec.ofInt 12 ((32 * block : Int) - 32)) =
      BitVec.ofNat 64 cursor := by
    rw [pointer, offsets.1]
    have rearrange : BitVec.ofNat 64 base + (BitVec.ofNat 64 (32 * block) - 32) =
        (BitVec.ofNat 64 base - 32) + BitVec.ofNat 64 (32 * block) := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [BitVec.add_comm (BitVec.ofNat 64 (32 * block)) (-32)]
    rw [rearrange]
    change BitVec.ofNat 64 base - BitVec.ofNat 64 32 + BitVec.ofNat 64 (32 * block) = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) base 32 (by decide) above,
      ← BitVec.ofNat_add]
  have destination : state.getReg .x8 + signExtend12 (BitVec.ofNat 12 (32 * block)) =
      BitVec.ofNat 64 (cursor + 32) := by
    rw [pointer, offsets.2, ← BitVec.ofNat_add]
    congr 1
    dsimp [cursor]
    omega
  apply streaming_machine_block _ state cursor
    (BitVec.ofInt 12 ((32 * block : Int) - 32)) (BitVec.ofNat 12 (32 * block))
    ready (by dsimp [cursor]; omega) (by dsimp [cursor]; omega)
  · apply commit_fetch _ (90 + 3 * block) _ (by omega)
    · rw [pc]; congr 1 <;> omega
    · rw [streaming_commit_code]
      interval_cases block <;> rfl
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, source,
      streamingFirstState]
  · apply commit_fetch _ (91 + 3 * block) _ (by omega)
    · change state.pc + 4 = _
      rw [pc]
      change BitVec.ofNat 64 (4456 + 12 * block) + BitVec.ofNat 64 4 = _
      rw [← BitVec.ofNat_add]; congr 1 <;> omega
    · rw [streaming_commit_code]
      interval_cases block <;> rfl
  · simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      streamingFirstState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x8), destination]
    change some (((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
      (BitVec.ofNat 64 (cursor + 32))).setPC (state.pc + 4 + 4)) =
      some (streamingArgsState state cursor)
    rw [BitVec.add_assoc]
    rfl
  · apply commit_fetch _ (92 + 3 * block) _ (by omega)
    · change state.pc + 8 = _
      rw [pc]
      change BitVec.ofNat 64 (4456 + 12 * block) + BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add]; congr 1 <;> omega
    · rw [streaming_commit_code]
      interval_cases block <;> rfl

/-- The eighth compression reads the last original block, then writes directly
to the caller's checked heap slot. It still costs three instructions/ten cycles. -/
theorem commit_heap_streaming_block (state : MachineState) (base : Nat)
    (pc : state.pc = 4540) (pointer : state.getReg .x8 = BitVec.ofNat 64 base)
    (ready : CommitLeafOracleReady state) (aligned : base % 8 = 0)
    (above : 32 ≤ base) (bounded : base + 256 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state (base + 192) 64)))
          let result ← execute (submission.image .commit) fuel
            (heapStreamingReplyState state (base + 192) answer) allowCoins
          return result.charge 10 1) := by
  have source : state.getReg .x8 + signExtend12 (192#12) =
      BitVec.ofNat 64 (base + 192) := by
    rw [pointer]
    change BitVec.ofNat 64 base + BitVec.ofNat 64 192 = _
    rw [BitVec.ofNat_add]
  apply heap_streaming_machine_block _ state (base + 192) 192 ready
    (by omega) (by omega) heapValid
  · apply commit_fetch _ 111 _ (by decide) pc
    rw [streaming_commit_code]; rfl
  · simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, source,
      heapStreamingFirstState]
  · apply commit_fetch _ 112 _ (by decide)
    · change state.pc + 4 = _; rw [pc]; rfl
    · rw [streaming_commit_code]; rfl
  · simp only [ordinaryStep, memoryArgumentsValid, memAccess, reduceIte, execInstrBr,
      heapStreamingFirstState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x23)]
    change some (((state.setReg .x10 (BitVec.ofNat 64 (base + 192))).setReg .x12
      (state.getReg .x23 + signExtend12 0)).setPC (state.pc + 4 + 4)) =
      some (heapStreamingArgsState state (base + 192))
    simp [signExtend12, heapStreamingArgsState, BitVec.add_assoc]
  · apply commit_fetch _ 113 _ (by decide)
    · change state.pc + 8 = _; rw [pc]; rfl
    · rw [streaming_commit_code]; rfl

/-- Execute any suffix of the seven streaming prefix blocks. Address setup is counted
explicitly, and the query continuation includes every possible compression reply. -/
theorem commit_streaming_loop (state : MachineState) (base first count : Nat)
    (blocks : first + count ≤ 7)
    (pc : state.pc = BitVec.ofNat 64 (4456 + 12 * first))
    (pointer : state.getReg .x8 = BitVec.ofNat 64 base)
    (ready : CommitLeafOracleReady state) (aligned : base % 8 = 0)
    (above : 32 ≤ base) (bounded : base + 256 ≤ MEMORY_BYTES)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3 * count + fuel) state allowCoins =
      (do let finished ← streamingMachineBlocks state (base - 32 + 32 * first) count
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge (10 * count) count) := by
  induction count generalizing state first with
  | zero => simp [streamingMachineBlocks, Execution.charge]
  | succ count ih =>
    rw [show 3 * (count + 1) + fuel = 3 + (3 * count + fuel) by omega,
      commit_streaming_block state base first (by omega) pc pointer ready aligned above bounded]
    simp only [streamingMachineBlocks, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    change BitVec 256 at answer
    let next := streamingReplyState state (base - 32 + 32 * first) answer
    have nextPC : next.pc = BitVec.ofNat 64 (4456 + 12 * (first + 1)) := by
      rw [streaming_reply_pc, pc]
      change BitVec.ofNat 64 (4456 + 12 * first) + BitVec.ofNat 64 12 = _
      rw [← BitVec.ofNat_add]
      congr 1 <;> omega
    have nextPointer : next.getReg .x8 = BitVec.ofNat 64 base :=
      (streaming_reply_register state _ answer .x8 (by decide)).trans pointer
    have nextReady : CommitLeafOracleReady next := by
      rcases ready with ⟨r5, r11, r13⟩
      exact ⟨(streaming_reply_register state _ answer .x5 (by decide)).trans r5,
        (streaming_reply_register state _ answer .x11 (by decide)).trans r11,
        (streaming_reply_register state _ answer .x13 (by decide)).trans r13⟩
    rw [ih next (first + 1) (by omega) nextPC nextPointer nextReady]
    rw [show base - 32 + 32 * first + 32 = base - 32 + 32 * (first + 1) by omega]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, next]

/-- The next salt prefix pointer moves with x8; unrelated registers are preserved. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [Reg.x8, .x21, .x10, .x12], finished.getReg reg = state.getReg reg := by
  simp only [commitLeafLoop, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨body, reached, rfl⟩ := reachable
  have regs := heap_streaming_machine_registers state _ count body reached
  constructor
  · change body.getReg .x8 + BitVec.ofNat 64 (32 * count) = _
    rw [regs.2 .x8 (by decide)]
  · intro reg preserved
    have not8 : .x8 ≠ reg := by intro h; subst reg; simp at preserved
    have not21 : .x21 ≠ reg := by intro h; subst reg; simp at preserved
    have untouched : reg ∉ [Reg.x10, .x12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved ⊢
      tauto
    simp only [commitLeafFinishState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ not21,
      MachineState.getReg_setReg_ne _ _ _ _ not8]
    exact regs.2 reg untouched

theorem commit_leaf_loop_chain (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x21 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) - 32 := by
  simp only [commitLeafLoop, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨body, reached, rfl⟩ := reachable
  change body.getReg .x8 + BitVec.ofNat 64 (32 * count) - 32 = _
  rw [(heap_streaming_machine_registers state _ count body reached).2 .x8 (by decide)]

theorem commit_leaf_loop_ready (state : MachineState) (count : Nat)
    (ready : CommitLeafOracleReady state) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    CommitLeafOracleReady finished := by
  have regs := (commit_leaf_loop_registers state count finished reachable).2
  exact ⟨(regs .x5 (by decide)).trans ready.1,
    (regs .x11 (by decide)).trans ready.2.1,
    (regs .x13 (by decide)).trans ready.2.2⟩

private def commitLeafFinishPrefix (state : MachineState) (count : Nat) : MachineState :=
  ([.ADDI .x8 .x8 256, .ADDI .x21 .x8 4064].take count).foldl execInstrBr state

/-- The actual tail advances the message base and records its last consumed
32-byte block as the chain pointer. Both additions cost one cycle. -/
theorem commit_leaf_finish (state : MachineState) (pc : state.pc = 4552)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel
            (commitLeafFinishState state 8) allowCoins
          return result.charge 2 0) := by
  have finish : commitLeafFinishPrefix state 2 = commitLeafFinishState state 8 := by
    simp only [commitLeafFinishPrefix, List.take, List.foldl, execInstrBr, signExtend12,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0)]
    change ((state.setReg .x8 (state.getReg .x8 + 256)).setReg .x21
      (state.getReg .x8 + 256 + 18446744073709551584)).setPC (state.pc + 4 + 4) =
        commitLeafFinishState state 8
    rw [show state.pc + 4 + 4 = state.pc + 8 by rw [BitVec.add_assoc]; rfl]
    have negate : (-32 : Word) = 18446744073709551584 := by decide
    rw [commitLeafFinishState, BitVec.sub_eq_add_neg, negate]
    rfl
  rw [← finish]
  apply execute_unit_steps (states := commitLeafFinishPrefix state)
  intro i hi
  refine ⟨.base (([.ADDI .x8 .x8 256, .ADDI .x21 .x8 4064][i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (114 + i) _ (by omega)
    · interval_cases i <;> simp [commitLeafFinishPrefix, execInstrBr, pc, MachineState.setPC]
    · rw [streaming_commit_code]
      interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4560)
    (link : state.getReg .x1 = 4316) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4348) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.JALR .x0 .x1 32)) := by
    apply commit_fetch _ 116 _ (by decide) pc
    rw [streaming_commit_code]
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 32)) = some (state.setPC 4348) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Twenty-four block instructions and three tail instructions hash one leaf
with exactly eight queries and 83 cycles, for every possible oracle reply. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc = 4456)
    (link : state.getReg .x1 = 4316)
    (ready : CommitLeafOracleReady state) (aligned : (state.getReg .x8).toNat % 8 = 0)
    (above : 32 ≤ (state.getReg .x8).toNat)
    (bounded : (state.getReg .x8).toNat + 256 ≤ MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32 = true ∧
      (state.getReg .x23).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (27 + fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafReadyState state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4348) allowCoins
          return result.charge 83 8) := by
  have entry : commitLeafReadyState state = state := by
    rw [commitLeafReadyState, ← pc, hoist_pc_self]
  rw [entry, show 27 + fuel = 3 * 7 + (3 + (2 + (1 + fuel))) by omega,
    commit_streaming_loop state (state.getReg .x8).toNat 0 7 (by decide)
      (by simpa using pc) (by simp) ready aligned above bounded]
  simp only [Nat.mul_zero, Nat.add_zero, commitLeafLoop, heapStreamingMachineBlocks,
    bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have regs := streaming_machine_registers state _ 7 body reached
  have lastPC : body.pc = 4540 := by rw [regs.1, pc]; rfl
  have lastPointer : body.getReg .x8 = BitVec.ofNat 64 (state.getReg .x8).toNat := by
    rw [regs.2 .x8 (by decide)]
    simp
  have lastReady : CommitLeafOracleReady body :=
    ⟨(regs.2 .x5 (by decide)).trans ready.1,
      (regs.2 .x11 (by decide)).trans ready.2.1,
      (regs.2 .x13 (by decide)).trans ready.2.2⟩
  have lastHeap : rangeValid (body.getReg .x23) 32 = true ∧
      (body.getReg .x23).toNat % 8 = 0 := by
    rw [regs.2 .x23 (by decide)]; exact heapValid
  rw [commit_heap_streaming_block body (state.getReg .x8).toNat lastPC lastPointer
    lastReady aligned above bounded lastHeap]
  rw [show (state.getReg .x8).toNat - 32 + 32 * 7 =
    (state.getReg .x8).toNat + 192 by omega]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  let final := heapStreamingReplyState body ((state.getReg .x8).toNat + 192) answer
  have endPC : final.pc = 4552 := by rw [heap_streaming_reply_pc, lastPC]; rfl
  have endLink : (commitLeafFinishState final 8).getReg .x1 = 4316 := by
    change final.getReg .x1 = _
    exact (heap_streaming_reply_register _ _ _ .x1 (by decide)).trans
      ((regs.2 .x1 (by decide)).trans link)
  have returnPC : (commitLeafFinishState final 8).pc = 4560 := by
    change final.pc + 8 = _
    rw [endPC]; rfl
  rw [commit_leaf_finish final endPC, commit_leaf_return _ returnPC endLink]
  simp [Execution.charge, ← Nat.add_assoc, final]

end CommitGolfCandidate
