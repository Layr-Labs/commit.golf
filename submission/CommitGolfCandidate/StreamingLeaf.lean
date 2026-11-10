import CommitGolfCandidate.DirectHeapExecution
import CommitGolfCandidate.CarriedPair

/-! Execution of the emitted commitment leaf with both address registers carried.
The first compression uses their ready values. Later blocks increment the pointers;
the final reply goes to the heap, and the tail prepares the next message leaf.
All memory bounds, fetched instructions and arbitrary replies are checked by the
actual interpreter bridge. -/
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
  [0x00060493#32, 0x00050613#32, 0x00058d13#32, 0x010009b7#32, 0x0180006f#32, 0x00000013#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x40000337#32, 0x0180006f#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00648933#32,
   0x20000337#32, 0x0180006f#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32,
   0x00000013#32, 0x00648bb3#32, 0x00200293#32, 0x00090513#32, 0x200005b7#32, 0x0180006f#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000073#32,
   0xfe060513#32, 0x00000293#32, 0x04000593#32, 0x00000693#32, 0x0180006f#32, 0x00000013#32,
   0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00000013#32, 0x00093303#32, 0x00653023#32,
   0x00893303#32, 0x00653423#32, 0x01093303#32, 0x00653823#32, 0x01893303#32, 0x00653c23#32,
   0x00000073#32, 0x02050513#32, 0x02060613#32, 0x00000073#32, 0x02050513#32, 0x02060613#32,
   0x00000073#32, 0x02050513#32, 0x02060613#32, 0x00000073#32, 0x02050513#32, 0x02060613#32,
   0x00000073#32, 0x02050513#32, 0x02060613#32, 0x00000073#32, 0x02050513#32, 0x02060613#32,
   0x00000073#32, 0x02050513#32, 0x000b8613#32, 0x00000073#32, 0x02050513#32, 0x02050613#32,
   0x02090913#32, 0x020b8b93#32, 0xf7a66ce3#32, 0xfff98a13#32, 0x020a0463#32, 0x006a1313#32,
   0x00648533#32, 0x005a1393#32, 0x00748633#32, 0x00000073#32, 0xfc050513#32, 0xfe060613#32,
   0xfffa0a13#32, 0xfe0a18e3#32, 0x0204b303#32, 0x006d3023#32, 0x0284b303#32, 0x006d3423#32,
   0x0304b303#32, 0x006d3823#32, 0x0384b303#32, 0x006d3c23#32, 0x00100293#32, 0x00000513#32,
   0x00000073#32] := by rfl



/-- The selector, compression width and primitive are fixed. The live address
registers are carried from the preceding leaf and incremented between queries. -/
abbrev CommitLeafOracleReady := StreamingOracleReady

def commitLeafReadyState (state : MachineState) : MachineState := state.setPC 4304

@[simp] theorem commit_leaf_ready_register (state : MachineState) (reg : Reg) :
    (commitLeafReadyState state).getReg reg = state.getReg reg := rfl

@[simp] theorem commit_leaf_ready_pc (state : MachineState) :
    (commitLeafReadyState state).pc = 4304 := rfl

@[simp] theorem commit_leaf_ready_oracle (state : MachineState)
    (ready : CommitLeafOracleReady state) :
    CommitLeafOracleReady (commitLeafReadyState state) := ready

/-- Keep the original message base explicit because queries change both argument registers. -/
def commitLeafFinishState (source : Word) (state : MachineState) (count : Nat) : MachineState :=
  ((state.setReg .x10 (source+BitVec.ofNat 64 (32*count)-32)).setReg .x12
    (source+BitVec.ofNat 64 (32*count))).setPC (state.pc+8)

def commitLeafLoop (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let finished ← heapStreamingMachineBlocks state ((state.getReg .x12).toNat-32) count
  return commitLeafFinishState (state.getReg .x12) finished count

/-- Pointer and PC updates preserve the direct-to-heap memory transform. -/
theorem commit_leaf_loop_memory (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (commitLeafLoop state count)).1.mem =
      (checkEvaluation oracle
        (heapStreamingBlocks state ((state.getReg .x12).toNat - 32) count (state.getReg .x23).toNat)).1.mem := by
  rw [commitLeafLoop, check_evaluation_bind]
  change (commitLeafFinishState (state.getReg .x12)
    (checkEvaluation oracle (heapStreamingMachineBlocks state ((state.getReg .x12).toNat - 32) count)).1
    count).mem = _
  change (checkEvaluation oracle
    (heapStreamingMachineBlocks state ((state.getReg .x12).toNat - 32) count)).1.mem = _
  exact (heap_streaming_machine_memory oracle state state _ count rfl).1

/-- The actual leaf's public-query accounting agrees with its memory reference. -/
theorem commit_leaf_loop_queries (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (commitLeafLoop state count)).2 = count := by
  rw [commitLeafLoop, check_evaluation_bind]
  change (checkEvaluation oracle
    (heapStreamingMachineBlocks state ((state.getReg .x12).toNat - 32) count)).2 + 0 = count
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
      accessValid (state.getReg .x12 + BitVec.ofNat 64 (8 * word)) 8 = true) :
    (state.getReg .x12).toNat % 8 = 0 ∧
      (state.getReg .x12).toNat + 256 ≤ MEMORY_BYTES := by
  have first := valid 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero, accessValid, rangeValid,
    Bool.and_eq_true, decide_eq_true_eq] at first
  have noWrap : (state.getReg .x12).toNat + 248 < 2^64 := by
    have bound := first.1
    unfold MEMORY_BYTES at bound
    omega
  have last := valid 31 (by decide)
  simp only [Nat.reduceMul, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq,
    BitVec.toNat_add] at last
  have finalNat : (state.getReg .x12).toNat + (248#64).toNat =
      (state.getReg .x12).toNat + 248 := rfl
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
    (blockBound : block<7) (positive : 1≤block)
    (pc : state.pc=BitVec.ofNat 64 (4304+12*block))
    (input : state.getReg .x10=BitVec.ofNat 64 (base-32+32*block)-32)
    (output : state.getReg .x12=BitVec.ofNat 64 (base-32+32*block))
    (ready : CommitLeafOracleReady state) (aligned : base%8=0)
    (above : 32≤base) (bounded : base+256≤MEMORY_BYTES) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state (base-32+32*block) 64)))
          let result ← execute (submission.image .commit) fuel
            (streamingReplyState state (base-32+32*block) answer) allowCoins
          return result.charge 10 1) := by
  let cursor := base-32+32*block
  have source : state.getReg .x10+signExtend12 (32#12)=BitVec.ofNat 64 cursor := by
    rw [input]
    exact BitVec.sub_add_cancel _ _
  have destination : state.getReg .x12+signExtend12 (32#12)=BitVec.ofNat 64 (cursor+32) := by
    rw [output]
    change BitVec.ofNat 64 cursor+BitVec.ofNat 64 32=BitVec.ofNat 64 (cursor+32)
    rw [← BitVec.ofNat_add]
  apply streaming_machine_block _ state cursor .x10 .x12 32 32 ready (by dsimp [cursor];omega)
    (by dsimp [cursor];omega)
  · apply commit_fetch _ (52+3*block) _ (by omega)
    · rw [pc];congr 1 <;> omega
    · rw [streaming_commit_code];interval_cases block <;> first | omega | rfl
  · simp only [ordinaryStep,memoryArgumentsValid,memAccess,reduceIte,execInstrBr]
    erw [source]
    rfl
  · apply commit_fetch _ (53+3*block) _ (by omega)
    · change state.pc+4=_
      rw [pc]
      change BitVec.ofNat 64 (4304+12*block)+BitVec.ofNat 64 4=_
      rw [← BitVec.ofNat_add];congr 1 <;> omega
    · rw [streaming_commit_code];interval_cases block <;> first | omega | rfl
  · simp only [ordinaryStep,memoryArgumentsValid,memAccess,reduceIte,execInstrBr,
      streamingFirstState,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10≠.x12)]
    erw [destination]
    change some (((state.setReg .x10 (BitVec.ofNat 64 cursor)).setReg .x12
      (BitVec.ofNat 64 (cursor+32))).setPC (state.pc+4+4))=some (streamingArgsState state cursor)
    rw [BitVec.add_assoc];rfl
  · apply commit_fetch _ (54+3*block) _ (by omega)
    · change state.pc+8=_
      rw [pc]
      change BitVec.ofNat 64 (4304+12*block)+BitVec.ofNat 64 8=_
      rw [← BitVec.ofNat_add];congr 1 <;> omega
    · rw [streaming_commit_code];interval_cases block <;> first | omega | rfl

/-- The final block increments its input and redirects the reply to the heap. -/
theorem commit_heap_streaming_block (state : MachineState) (base : Nat)
    (pc : state.pc=4388) (input : state.getReg .x10=BitVec.ofNat 64 (base+192)-32)
    (ready : CommitLeafOracleReady state) (aligned : base%8=0)
    (above : 32≤base) (bounded : base+256≤MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32=true ∧ (state.getReg .x23).toNat%8=0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state (base+192) 64)))
          let result ← execute (submission.image .commit) fuel
            (heapStreamingReplyState state (base+192) answer) allowCoins
          return result.charge 10 1) := by
  have source : state.getReg .x10+signExtend12 (32#12)=BitVec.ofNat 64 (base+192) := by
    rw [input];exact BitVec.sub_add_cancel _ _
  apply heap_streaming_machine_block _ state (base+192) .x10 32 ready (by omega) (by omega) heapValid
  · apply commit_fetch _ 73 _ (by decide) pc
    rw [streaming_commit_code];rfl
  · simp only [ordinaryStep,memoryArgumentsValid,memAccess,reduceIte,execInstrBr]
    erw [source]
    rfl
  · apply commit_fetch _ 74 _ (by decide)
    · change state.pc+4=4392
      rw [pc];rfl
    · rw [streaming_commit_code];rfl
  · simp only [ordinaryStep,memoryArgumentsValid,memAccess,reduceIte,execInstrBr,
      heapStreamingFirstState,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10≠.x23)]
    rw [show signExtend12 (0 : BitVec 12)=0#64 by decide,BitVec.add_zero]
    change some (((state.setReg .x10 (BitVec.ofNat 64 (base+192))).setReg .x12
      (state.getReg .x23)).setPC (state.pc+4+4))=some (heapStreamingArgsState state (base+192))
    rw [BitVec.add_assoc];rfl
  · apply commit_fetch _ 75 _ (by decide)
    · change state.pc+8=4396
      rw [pc];rfl
    · rw [streaming_commit_code];rfl

theorem commit_streaming_loop (state : MachineState) (base first count : Nat)
    (blocks : first+count≤7) (positive : 1≤first)
    (pc : state.pc=BitVec.ofNat 64 (4304+12*first))
    (input : state.getReg .x10=BitVec.ofNat 64 (base-32+32*first)-32)
    (output : state.getReg .x12=BitVec.ofNat 64 (base-32+32*first))
    (ready : CommitLeafOracleReady state) (aligned : base%8=0)
    (above : 32≤base) (bounded : base+256≤MEMORY_BYTES) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3*count+fuel) state allowCoins =
      (do let finished ← streamingMachineBlocks state (base-32+32*first) count
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge (10*count) count) := by
  induction count generalizing state first with
  | zero => simp [streamingMachineBlocks,Execution.charge]
  | succ count ih =>
    rw [show 3*(count+1)+fuel=3+(3*count+fuel) by omega,
      commit_streaming_block state base first (by omega) positive pc input output ready aligned above bounded]
    simp only [streamingMachineBlocks,bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro answer _
    change BitVec 256 at answer
    let next := streamingReplyState state (base-32+32*first) answer
    have nextPC : next.pc=BitVec.ofNat 64 (4304+12*(first+1)) := by
      rw [streaming_reply_pc,pc]
      change BitVec.ofNat 64 (4304+12*first)+BitVec.ofNat 64 12=_
      rw [← BitVec.ofNat_add];congr 1 <;> omega
    have nextInput : next.getReg .x10=BitVec.ofNat 64 (base-32+32*(first+1))-32 := by
      change BitVec.ofNat 64 (base-32+32*first)=_
      rw [show base-32+32*(first+1)=(base-32+32*first)+32 by omega]
      conv_rhs => rw [BitVec.ofNat_add]
      erw [BitVec.add_sub_cancel]
    have nextOutput : next.getReg .x12=BitVec.ofNat 64 (base-32+32*(first+1)) := by
      change BitVec.ofNat 64 (base-32+32*first+32)=_
      congr 1 <;> omega
    have nextReady : CommitLeafOracleReady next :=
      ⟨(streaming_reply_register state _ answer .x5 (by decide)).trans ready.1,
        (streaming_reply_register state _ answer .x11 (by decide)).trans ready.2.1,
        (streaming_reply_register state _ answer .x13 (by decide)).trans ready.2.2⟩
    rw [ih next (first+1) (by omega) (by omega) nextPC nextInput nextOutput nextReady]
    rw [show base-32+32*first+32=base-32+32*(first+1) by omega]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,next]

/-- Both address registers are carried, so the first block is just ECALL. -/
theorem commit_streaming_first (state : MachineState) (base : Nat)
    (pc : state.pc=4312) (pointer : state.getReg .x12=BitVec.ofNat 64 base)
    (input : state.getReg .x10=BitVec.ofNat 64 (base-32))
    (ready : CommitLeafOracleReady state) (aligned : base%8=0)
    (above : 32≤base) (bounded : base+256≤MEMORY_BYTES) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1+fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state (base-32) 64)))
          let result ← execute (submission.image .commit) fuel
            (streamingReplyState (state.setPC 4304) (base-32) answer) allowCoins
          return result.charge 8 1) := by
  have virtual : state.setPC (state.pc-8)=state.setPC 4304 := by rw [pc];rfl
  rw [← virtual]
  apply streaming_carried_pair _ state (base-32) input (by
    rw [show base-32+32=base by omega];exact pointer) ready (by omega) (by omega)
  apply commit_fetch _ 54 _ (by decide) pc
  rw [streaming_commit_code];rfl

/-- One direct first query followed by six incremented prefix blocks. -/
theorem commit_carried_prefix (state : MachineState) (base : Nat)
    (pc : state.pc=4304) (pointer : state.getReg .x12=BitVec.ofNat 64 base)
    (input : state.getReg .x10=BitVec.ofNat 64 (base-32))
    (ready : CommitLeafOracleReady state) (aligned : base%8=0)
    (above : 32≤base) (bounded : base+256≤MEMORY_BYTES) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (19+fuel) (state.setPC 4312) allowCoins =
      (do let finished ← streamingMachineBlocks state (base-32) 7
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge 68 7) := by
  rw [show 19+fuel=1+(3*6+fuel) by omega,
    commit_streaming_first (state.setPC 4312) base rfl pointer input ready aligned above bounded]
  have same : (state.setPC 4312).setPC 4304=state := by
    rw [← pc]
    change state.setPC state.pc=state
    exact hoist_pc_self state
  rw [same]
  have memory : readBuffer (state.setPC 4312) (base-32) 64=readBuffer state (base-32) 64 :=
    read_buffer_memory_congr _ _ rfl _ _
  rw [memory,streamingMachineBlocks]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  let next := streamingReplyState state (base-32) answer
  have nextPC : next.pc=BitVec.ofNat 64 (4304+12*1) := by rw [streaming_reply_pc,pc];rfl
  have nextInput : next.getReg .x10=BitVec.ofNat 64 (base-32+32*1)-32 := by
    change BitVec.ofNat 64 (base-32)=_
    rw [show base-32+32*1=base by omega]
    exact (BitVec.ofNat_sub_ofNat_of_le (w := 64) base 32 (by decide) above).symm
  have nextOutput : next.getReg .x12=BitVec.ofNat 64 (base-32+32*1) := by rfl
  have nextReady : CommitLeafOracleReady next :=
    ⟨(streaming_reply_register state _ answer .x5 (by decide)).trans ready.1,
      (streaming_reply_register state _ answer .x11 (by decide)).trans ready.2.1,
      (streaming_reply_register state _ answer .x13 (by decide)).trans ready.2.2⟩
  rw [show base-32+32=base-32+32*1 by omega,
    commit_streaming_loop next base 1 6 (by decide) (by decide) nextPC nextInput nextOutput nextReady aligned above bounded]
  simp [Execution.charge,← Nat.add_assoc,next]

/-- The next salt prefix pointer moves with x8; unrelated registers are preserved. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x12=state.getReg .x12+BitVec.ofNat 64 (32*count) ∧
    ∀ reg ∉ [Reg.x10,.x12],finished.getReg reg=state.getReg reg := by
  simp only [commitLeafLoop,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨body,reached,rfl⟩ := reachable
  have regs := heap_streaming_machine_registers state _ count body reached
  constructor
  · rfl
  · intro reg preserved
    have not10 : .x10≠reg := by intro h;subst reg;simp at preserved
    have not12 : .x12≠reg := by intro h;subst reg;simp at preserved
    simp only [commitLeafFinishState,MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ not12,
      MachineState.getReg_setReg_ne _ _ _ _ not10]
    exact regs.2 reg preserved

theorem commit_leaf_loop_chain (state : MachineState) (count : Nat)
    (finished : MachineState) (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x10=state.getReg .x12+BitVec.ofNat 64 (32*count)-32 := by
  simp only [commitLeafLoop,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨body,reached,rfl⟩ := reachable
  rfl

theorem commit_leaf_loop_ready (state : MachineState) (count : Nat)
    (ready : CommitLeafOracleReady state) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    CommitLeafOracleReady finished := by
  have regs := (commit_leaf_loop_registers state count finished reachable).2
  exact ⟨(regs .x5 (by decide)).trans ready.1,
    (regs .x11 (by decide)).trans ready.2.1,
    (regs .x13 (by decide)).trans ready.2.2⟩

private def commitLeafFinishPrefix (state : MachineState) (count : Nat) : MachineState :=
  ([.ADDI .x10 .x10 32,.ADDI .x12 .x10 32].take count).foldl execInstrBr state

/-- The two tail instructions prepare both pointers for the next message leaf. -/
theorem commit_leaf_finish (state : MachineState) (source : Word) (pc : state.pc=4400)
    (input : state.getReg .x10=source+192) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (2+fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafFinishState source state 8) allowCoins
          return result.charge 2 0) := by
  have finish : commitLeafFinishPrefix state 2=commitLeafFinishState source state 8 := by
    simp only [commitLeafFinishPrefix,List.take,List.foldl,execInstrBr,signExtend12,
      MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide : Reg.x10≠.x0)]
    change ((state.setReg .x10 (state.getReg .x10+32)).setReg .x12
      (state.getReg .x10+32+32)).setPC (state.pc+4+4)=commitLeafFinishState source state 8
    rw [input]
    have chain : source+192+32=source+256-32 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
      rfl
    have output : source+192+32+32=source+256 := by
      simp only [BitVec.add_assoc]
      rfl
    rw [output,chain]
    rw [show state.pc+4+4=state.pc+8 by rw [BitVec.add_assoc];rfl]
    rfl
  rw [← finish]
  apply execute_unit_steps (states := commitLeafFinishPrefix state)
  intro i hi
  refine ⟨.base (([.ADDI .x10 .x10 32,.ADDI .x12 .x10 32][i]?).getD .EBREAK),?_,?_,?_⟩
  · apply commit_fetch _ (76+i) _ (by omega)
    · interval_cases i <;> simp [commitLeafFinishPrefix,execInstrBr,pc,MachineState.setPC]
    · rw [streaming_commit_code];interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (0 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4408) allowCoins
          return result.charge 0 0) := by
  rw [← pc, hoist_pc_self]
  simp [Execution.charge]

/-- Twenty-two block instructions and two tail instructions hash one leaf
with exactly eight queries and eighty cycles. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc=4312)
    (input : state.getReg .x10=BitVec.ofNat 64 ((state.getReg .x12).toNat-32))
    (ready : CommitLeafOracleReady state) (aligned : (state.getReg .x12).toNat%8=0)
    (above : 32≤(state.getReg .x12).toNat) (bounded : (state.getReg .x12).toNat+256≤MEMORY_BYTES)
    (heapValid : rangeValid (state.getReg .x23) 32=true ∧ (state.getReg .x23).toNat%8=0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (24+fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafReadyState state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4408) allowCoins
          return result.charge 80 8) := by
  let virtual := commitLeafReadyState state
  have virtualPC : virtual.pc=4304 := rfl
  have actual : virtual.setPC 4312=state := by
    unfold virtual commitLeafReadyState
    rw [← pc]
    change state.setPC state.pc=state
    exact hoist_pc_self state
  have prefixRun := commit_carried_prefix virtual (state.getReg .x12).toNat virtualPC
    (by simp [virtual]) input ready aligned above bounded (3+(2+fuel)) allowCoins
  rw [actual] at prefixRun
  rw [show 24+fuel=19+(3+(2+fuel)) by omega,prefixRun]
  simp only [commitLeafLoop,heapStreamingMachineBlocks,commit_leaf_ready_register,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro body reached
  have regs := streaming_machine_registers virtual _ 7 body reached
  have addresses := streaming_machine_addresses virtual ((state.getReg .x12).toNat-32) 6 body reached
  have lastPC : body.pc=4388 := by rw [regs.1,virtualPC];rfl
  have lastInput : body.getReg .x10=BitVec.ofNat 64 ((state.getReg .x12).toNat+192)-32 := by
    rw [addresses.1]
    rw [show (state.getReg .x12).toNat+192=(state.getReg .x12).toNat-32+32*6+32 by omega]
    conv_rhs => rw [BitVec.ofNat_add]
    erw [BitVec.add_sub_cancel]
  have lastReady : CommitLeafOracleReady body :=
    ⟨(regs.2 .x5 (by decide)).trans ready.1,
      (regs.2 .x11 (by decide)).trans ready.2.1,
      (regs.2 .x13 (by decide)).trans ready.2.2⟩
  have lastHeap : rangeValid (body.getReg .x23) 32=true ∧ (body.getReg .x23).toNat%8=0 := by
    rw [regs.2 .x23 (by decide)];exact heapValid
  rw [commit_heap_streaming_block body (state.getReg .x12).toNat lastPC lastInput
    lastReady aligned above bounded lastHeap]
  rw [show (state.getReg .x12).toNat-32+32*7=(state.getReg .x12).toNat+192 by omega]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  change BitVec 256 at answer
  let final := heapStreamingReplyState body ((state.getReg .x12).toNat+192) answer
  have endPC : final.pc=4400 := by rw [heap_streaming_reply_pc,lastPC];rfl
  have endInput : final.getReg .x10=state.getReg .x12+192 := by
    change BitVec.ofNat 64 ((state.getReg .x12).toNat+192)=state.getReg .x12+192
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat]
    rfl
  have returnPC : (commitLeafFinishState (state.getReg .x12) final 8).pc=4408 := by
    change final.pc+8=_
    rw [endPC];rfl
  rw [commit_leaf_finish final (state.getReg .x12) endPC endInput]
  have samePC : (commitLeafFinishState (state.getReg .x12) final 8).setPC 4408=
      commitLeafFinishState (state.getReg .x12) final 8 := by
    rw [← returnPC,hoist_pc_self]
  rw [samePC]
  simp [Execution.charge,← Nat.add_assoc,final]

end CommitGolfCandidate
