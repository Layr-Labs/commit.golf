import CommitGolfCandidate.DirectHeapExecution

/-! Retained explicit-window commitment reference and shared address bounds.
The fused carried-input image is linked by FusedImage; the reference advances x8/x21
virtually so existing memory and security refinements remain reusable. -/
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

end CommitGolfCandidate
