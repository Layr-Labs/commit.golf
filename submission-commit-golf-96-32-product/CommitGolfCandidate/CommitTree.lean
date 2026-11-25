import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete parent loop on the gap heap (sixteen parents per iteration), the
fifteen-node root tail, the root output copy, and the successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- `remaining` 16-parent loop iterations, followed by the 15-node root tail. -/
def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => parentTailRun state
  | state, remaining + 1 => do
      let next ← parentIterationRun state
      commitParents next remaining

/-- Pointer registers of the parent loop with `remaining` 16-parent iterations left:
the next iteration computes nodes `16r + 15` down to `16r`. -/
structure ParentPointers (state : MachineState) (base remaining : Nat) : Prop where
  heap : state.getReg .x9 = BitVec.ofNat 64 base
  left : state.getReg .x21 = BitVec.ofNat 64 (base + 1536 * remaining)
  right : state.getReg .x22 = BitVec.ofNat 64 (base + 768 * remaining)

/-- Safety and loop-control conditions of the parent loop, independent of memory. -/
structure ParentLoopInvariant (state : MachineState) (base remaining : Nat) : Prop where
  pointers : ParentPointers state base remaining
  pc : state.pc = if remaining = 0 then 7116 else 6912
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  aligned : base % 8 = 0
  bound : base + 1536 * remaining + 1536 ≤ MEMORY_BYTES

/-- Concrete addresses of parent call `j` in the loop (`isTail = false`) or tail (`isTail = true`). -/
theorem parent_addresses (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining)
    (bound : base + 1536 * remaining + 1536 ≤ MEMORY_BYTES)
    (isTail : Bool) (j : Nat) (hj : j < 16) :
    (parentSource state isTail j).toNat =
      base + (if isTail then 0 else 1536 * remaining) + 96 * (15 - j) ∧
    (parentOutput state isTail j).toNat =
      base + (if isTail then 0 else 768 * remaining) + heapOffset (15 - j) := by
  have hkOff : heapOffset (15 - j) + 32 ≤ 768 := by unfold heapOffset; omega
  cases isTail
  · refine ⟨?_, ?_⟩
    · show (state.getReg .x21 + BitVec.ofNat 64 (96 * (15 - j))).toNat = _
      rw [pointers.left]; exact pointer_offset_nat _ _ (by omega)
    · show (state.getReg .x22 + BitVec.ofNat 64 (heapOffset (15 - j))).toNat = _
      rw [pointers.right]; exact pointer_offset_nat _ _ (by omega)
  · refine ⟨?_, ?_⟩
    · show (state.getReg .x9 + BitVec.ofNat 64 (96 * (15 - j))).toNat = _
      rw [pointers.heap]; simp only [↓reduceIte, Nat.add_zero]; exact pointer_offset_nat _ _ (by omega)
    · show (state.getReg .x9 + BitVec.ofNat 64 (heapOffset (15 - j))).toNat = _
      rw [pointers.heap]; simp only [↓reduceIte, Nat.add_zero]; exact pointer_offset_nat _ _ (by omega)

theorem parent_call_valid_nat (state : MachineState) (isTail : Bool) (j source output : Nat)
    (hs : (parentSource state isTail j).toNat = source)
    (ho : (parentOutput state isTail j).toNat = output)
    (sourceBound : source + 96 ≤ MEMORY_BYTES) (outputBound : output + 32 ≤ MEMORY_BYTES)
    (sourceAligned : source % 8 = 0) (outputAligned : output % 8 = 0) :
    ParentCallValid state isTail j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, hs, decide_eq_true_eq]; omega
  · rw [hs]; exact sourceAligned
  · simp only [rangeValid, ho, decide_eq_true_eq]; omega
  · rw [ho]; exact outputAligned

theorem parent_next_registers (state : MachineState) :
    (parentNextState state).getReg .x21 = state.getReg .x21 - 1536 ∧
    (parentNextState state).getReg .x22 = state.getReg .x22 - 768 ∧
    (parentNextState state).pc =
      (if state.getReg .x22 - 768 = state.getReg .x9 then 7116 else 6912) ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x22 → (parentNextState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      MachineState.getReg_setReg_eq (by decide)]
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
  · intro reg n21 n22
    rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21)]

/-- Registers after one 16-parent iteration (any oracle answers). -/
theorem parent_iteration_registers (state finished : MachineState)
    (reachable : finished ∈ support (parentIterationRun state)) :
    finished.getReg .x21 = state.getReg .x21 - 1536 ∧
    finished.getReg .x22 = state.getReg .x22 - 768 ∧
    finished.pc = (if state.getReg .x22 - 768 = state.getReg .x9 then 7116 else 6912) ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x21 → reg ≠ .x22 →
      finished.getReg reg = state.getReg reg := by
  obtain ⟨hashed, hh, rfl⟩ := parent_iteration_support state finished reachable
  have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
      hashed.getReg reg = state.getReg reg :=
    parent_calls_from_register state hashed false 0 16 hh reg n10 n12
  have next := parent_next_registers hashed
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.1, keep .x21 (by decide) (by decide)]
  · rw [next.2.1, keep .x22 (by decide) (by decide)]
  · rw [next.2.2.1, keep .x22 (by decide) (by decide), keep .x9 (by decide) (by decide)]
  · intro reg n10 n12 n21 n22
    rw [next.2.2.2 reg n21 n22, keep reg n10 n12]

theorem word_sub_literal (a b : Nat) (le : b ≤ a) (small : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  BitVec.ofNat_sub_ofNat_of_le (w := 64) a b small le

theorem parent_loop_next_invariant (state finished : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base (remaining + 1))
    (reachable : finished ∈ support (parentIterationRun state)) :
    ParentLoopInvariant finished base remaining := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have regs := parent_iteration_registers state finished reachable
  have bound := invariant.bound
  have p := invariant.pointers
  have x21 : finished.getReg .x21 = BitVec.ofNat 64 (base + 1536 * remaining) := by
    rw [regs.1, p.left]
    show BitVec.ofNat 64 (base + 1536 * (remaining + 1)) - BitVec.ofNat 64 1536 = _
    have hmul : base + 1536 * (remaining + 1) = base + 1536 * remaining + 1536 := by
      rw [Nat.mul_succ, Nat.add_assoc]
    rw [hmul, word_sub_literal _ _ (Nat.le_add_left 1536 _) (by decide), Nat.add_sub_cancel]
  have sub22 : state.getReg .x22 - 768 = BitVec.ofNat 64 (base + 768 * remaining) := by
    rw [p.right]
    show BitVec.ofNat 64 (base + 768 * (remaining + 1)) - BitVec.ofNat 64 768 = _
    have hmul : base + 768 * (remaining + 1) = base + 768 * remaining + 768 := by
      rw [Nat.mul_succ, Nat.add_assoc]
    rw [hmul, word_sub_literal _ _ (Nat.le_add_left 768 _) (by decide), Nat.add_sub_cancel]
  have x22 : finished.getReg .x22 = BitVec.ofNat 64 (base + 768 * remaining) := regs.2.1.trans sub22
  have x9 : finished.getReg .x9 = BitVec.ofNat 64 base :=
    (regs.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)).trans p.heap
  have boundNext : base + 1536 * remaining + 1536 ≤ MEMORY_BYTES := by
    rw [Nat.mul_succ] at bound; generalize 1536 * remaining = k at bound ⊢; omega
  refine ⟨⟨x9, x21, x22⟩, ?_, ?_, ?_, ?_, invariant.aligned, boundNext⟩
  · rw [regs.2.2.1, sub22, p.heap]
    by_cases zero : remaining = 0
    · subst zero
      simp
    · rw [if_neg, if_neg zero]
      intro same
      have := congrArg BitVec.toNat same
      rw [word_small_toNat _ (by omega), word_small_toNat _ (by omega)] at this
      omega
  · exact (regs.2.2.2 .x5 (by decide) (by decide) (by decide) (by decide)).trans invariant.r5
  · exact (regs.2.2.2 .x11 (by decide) (by decide) (by decide) (by decide)).trans invariant.r11
  · exact (regs.2.2.2 .x13 (by decide) (by decide) (by decide) (by decide)).trans invariant.r13

attribute [local irreducible] execute parentIterationRun parentTailRun parentCallState

/-- All 16-parent iterations, then the 15-node root tail. Each iteration costs 51
instructions, 163 cycles and 16 queries; the tail costs 45 instructions, 150 cycles
and 15 queries. -/
theorem commit_parents (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining) (fuel : Nat) :
    execute (submission.image .commit) (51 * remaining + 45 + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (163 * remaining + 150) (16 * remaining + 15)) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction remaining generalizing state with
  | zero =>
    have bound := invariant.bound
    have aligned := invariant.aligned
    have valid : ∀ k < 15, ParentCallValid state true k := by
      intro k hk
      have addr := parent_addresses state base 0 invariant.pointers invariant.bound true k (by omega)
      simp only [↓reduceIte, Nat.add_zero] at addr
      have hOff : heapOffset (15 - k) + 32 ≤ 768 := by unfold heapOffset; omega
      have hAlign : heapOffset (15 - k) % 8 = 0 := heap_offset_aligned (15 - k)
      exact parent_call_valid_nat state true k _ _ addr.1 addr.2
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = 7116 := by rw [invariant.pc]; rfl
    rw [show 51 * 0 + 45 + fuel = 45 + fuel by omega,
      commit_parent_tail state pc invariant.r5 invariant.r11 invariant.r13 valid]
    simp only [commitParents, Nat.mul_zero, Nat.zero_add]
  | succ remaining ih =>
    have bound := invariant.bound
    have aligned := invariant.aligned
    have valid : ∀ k < 16, ParentCallValid state false k := by
      intro k hk
      have addr := parent_addresses state base (remaining + 1) invariant.pointers invariant.bound
        false k hk
      simp only [Bool.false_eq_true, ↓reduceIte] at addr
      have hOff : heapOffset (15 - k) + 32 ≤ 768 := by unfold heapOffset; omega
      have hAlign : heapOffset (15 - k) % 8 = 0 := heap_offset_aligned (15 - k)
      exact parent_call_valid_nat state false k _ _ addr.1 addr.2
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = 6912 := by rw [invariant.pc]; rfl
    rw [show 51 * (remaining + 1) + 45 + fuel = 51 + (51 * remaining + 45 + fuel) by omega,
      commit_parent_iteration state pc invariant.r5 invariant.r11 invariant.r13 valid]
    simp only [commitParents, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (parent_loop_next_invariant state next base remaining invariant reached)]
    simp only [bind_assoc, pure_bind]
    apply bind_congr_of_forall_mem_support
    intro finished _
    apply bind_congr_of_forall_mem_support
    intro result _
    simp only [Execution.charge, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The parent loop and root tail reach the root copy (`pc = 7296`) and preserve its pointers. -/
theorem commit_parents_finished (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    finished.pc = 7296 ∧
    ∀ reg ∈ [Reg.x9, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    rw [commitParents] at reachable
    have hreach : finished ∈ support (parentCallsFrom state true 0 15) := by
      unfold parentTailRun at reachable; exact reachable
    refine ⟨?_, ?_⟩
    · have hpc := parent_calls_from_pc state finished true 0 15 (by decide)
        (by rw [invariant.pc]; rfl) hreach
      simpa [parentCallIndex] using hpc
    · intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact parent_calls_from_register state finished true 0 15 hreach _ (by decide) (by decide)
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (parent_loop_next_invariant state next base remaining invariant reached) rest
    have regs := parent_iteration_registers state next reached
    refine ⟨done.1, fun reg member => (done.2 reg member).trans ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact regs.2.2.2 _ (by decide) (by decide) (by decide) (by decide)

/-- Copy the root from heap node one into the public commitment buffer, then halt
successfully. This costs eleven cycles and makes no oracle queries. -/
theorem commit_root (state : MachineState) (pc : state.pc = 7296)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state .x9 .x26 32 0), 11, 0⟩ := by
  have copyPC : state.pc = BitVec.ofNat 64 (4096 + 4 * 800) := by rw [pc]; rfl
  have nextPC : (commitCopyState state .x9 .x26 32 0).pc = 7328 := by
    rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 800 .x9 .x26 32 0 (by decide)
      (fun i hi => commit_instr_root_copy i hi) copyPC (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) rootValid
      (fun word => by simpa using outputValid word),
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled:
`count/32` 32-leaf iterations, `count/16 - 1` 16-parent iterations and the 15-node tail,
root output. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state (count / 32)
  let parents ← commitParents (commitParentsStartState leaves) (count / 16 - 1)
  return commitExitState (commitCopyState parents .x9 .x26 32 0)

attribute [local irreducible] commitLeaves commitParents commitCopyState

/-- The heap word accesses of the root copy. -/
theorem heap_word_access (heap : Word) (base offset : Nat) (heapPointer : heap = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (offsetAligned : offset % 8 = 0) (bound : base + offset + 8 ≤ MEMORY_BYTES) :
    accessValid (heap + BitVec.ofNat 64 offset) 8 = true := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  simp only [accessValid, rangeValid, heapPointer, pointer_offset_nat base offset (by omega),
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- Exact execution of all leaves, all parents, the root and root output for the
actual tree of `2^24` leaves. Safety conditions constrain addresses only; the theorem
covers every message and salt. -/
theorem commit_body (state : MachineState) (base : Nat)
    (leaves : CommitLeavesInvariant state (2 ^ 19))
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base + 96 * 2 ^ 24 ≤ MEMORY_BYTES)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (393216022 + fuel) state true =
      (do let finished ← commitBody state (2 ^ 24)
          return ⟨.success, finished, 980418575, 5 * 2 ^ 24 - 1⟩) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have hsteps : 393216022 + fuel =
      648 * 2 ^ 19 + (17 + (51 * (2 ^ 20 - 1) + 45 + (11 + fuel))) := by
    have hc : 393216022 = 648 * 2 ^ 19 + (17 + (51 * (2 ^ 20 - 1) + 45 + 11)) := by norm_num
    rw [hc, Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
  rw [hsteps, commit_leaves state (2 ^ 19) leaves]
  have div32 : (2 ^ 24 : Nat) / 32 = 2 ^ 19 := by norm_num
  have div16 : (2 ^ 24 : Nat) / 16 - 1 = 2 ^ 20 - 1 := by norm_num
  unfold commitBody
  rw [div32, div16]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state (2 ^ 19) leaves hashed reached
  have start := commit_parents_start_state hashed leafDone.1
  have hashedReg (reg : Reg) (member : reg ∈ [Reg.x9, .x26, .x5, .x11, .x13]) :
      (commitParentsStartState hashed).getReg reg = state.getReg reg := by
    have notStart : reg ≠ .x6 ∧ reg ≠ .x21 ∧ reg ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [start.2.2.2.2 reg notStart.1 notStart.2.1 notStart.2.2, leafDone.2 reg member]
  have x9 : (commitParentsStartState hashed).getReg .x9 = BitVec.ofNat 64 base :=
    (hashedReg .x9 (by simp)).trans heapPointer
  have invariant : ParentLoopInvariant (commitParentsStartState hashed) base (2 ^ 20 - 1) := by
    have hbound : base + 1536 * (2 ^ 20 - 1) + 1536 ≤ MEMORY_BYTES := by
      rw [Nat.add_assoc, show 1536 * (2 ^ 20 - 1) + 1536 = 96 * 2 ^ 24 by norm_num]
      exact bound
    refine ⟨⟨x9, ?_, ?_⟩, ?_, ?_, ?_, ?_, aligned, hbound⟩
    · rw [start.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 1536 * (2 ^ 20 - 1) = base + 1610611200 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 768 * (2 ^ 20 - 1) = base + 805305600 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.2.1, if_neg (by norm_num)]
    · exact (hashedReg .x5 (by simp)).trans leaves.r5
    · exact (hashedReg .x11 (by simp)).trans leaves.r11
    · exact (hashedReg .x13 (by simp)).trans leaves.r13
  rw [commit_parents_start hashed leafDone.1,
    commit_parents (commitParentsStartState hashed) base (2 ^ 20 - 1) invariant]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished _ base (2 ^ 20 - 1) invariant finished reachedParents
  have finishedHeap : finished.getReg .x9 = BitVec.ofNat 64 base :=
    (parentDone.2 .x9 (by simp)).trans x9
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    intro word
    have := word.isLt
    exact heap_word_access _ base _ finishedHeap aligned (by omega) (by omega)
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), hashedReg .x26 (by simp)]; exact outputValid
  rw [commit_root finished parentDone.1 root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  norm_num

end CommitGolfCandidate
