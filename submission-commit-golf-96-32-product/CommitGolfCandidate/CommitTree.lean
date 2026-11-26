import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete 32-parent descending loop, 31-parent tail (down to root node 1),
root output copy, and successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- `remaining` 32-parent loop iterations, followed by the 31-parent tail (nodes 31..1). -/
def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => parentCallsRun state 0 31
  | state, remaining + 1 => do
      let next ← parentIterationRun state
      commitParents next remaining

/-- Pointer registers of the 32-parent loop with `remaining` blocks left:
`x21 = base + 3072*remaining + 1536`, `x22 = base + 1536*remaining`, `x24 = 3072`. -/
structure ParentPointers (state : MachineState) (base remaining : Nat) : Prop where
  heap : state.getReg .x9 = BitVec.ofNat 64 base
  src : state.getReg .x21 = BitVec.ofNat 64 (base + 3072 * remaining + 1536)
  dst : state.getReg .x22 = BitVec.ofNat 64 (base + 1536 * remaining)
  stride : state.getReg .x24 = 3072

/-- Safety and loop-control conditions of the 32-parent loop. -/
structure ParentLoopInvariant (state : MachineState) (base remaining : Nat) : Prop where
  pointers : ParentPointers state base remaining
  pc : state.pc = if remaining = 0 then 6864 else 6468
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  aligned : base % 8 = 0
  bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES

/-- Concrete source and output addresses of parent offset `u < 32`. -/
theorem parent_addresses (state : MachineState) (base remaining u : Nat)
    (hu : u < 32) (pointers : ParentPointers state base remaining)
    (bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES) :
    (parentSource state u).toNat = base + 96 * (32 * remaining + u) ∧
    (parentOutput state u).toNat = base + heapOffset (32 * remaining + u) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have hOff : heapOffset (32 * remaining + u) = 1536 * remaining + heapOffset u := by
    unfold heapOffset; omega
  have hOffU : heapOffset u + 32 ≤ 1536 := by
    have := heap_offset_bound u 16 (by omega); omega
  constructor
  · unfold parentSource
    rw [pointers.src]
    have hsplit : BitVec.ofNat 64 (base + 3072 * remaining + 1536) =
        BitVec.ofNat 64 (base + 3072 * remaining) + BitVec.ofNat 64 1536 := by
      rw [← BitVec.ofNat_add]
    rw [hsplit, BitVec.add_assoc, signExtend12_parentSrc ⟨u, hu⟩,
      pointer_offset_nat (base + 3072 * remaining) (96 * u) (by omega)]
    omega
  · unfold parentOutput
    rw [pointers.dst, pointer_offset_nat (base + 1536 * remaining) (heapOffset u) (by omega), hOff]
    omega

theorem parent_call_valid_of_pointers (state : MachineState) (base remaining u : Nat)
    (hu : u < 32) (pointers : ParentPointers state base remaining)
    (aligned : base % 8 = 0) (bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES) :
    ParentCallValid state u := by
  have addr := parent_addresses state base remaining u hu pointers bound
  have hOffAl : heapOffset (32 * remaining + u) % 8 = 0 := heap_offset_aligned _
  have hOffB : heapOffset (32 * remaining + u) + 32 ≤ 1536 * remaining + 1536 := by
    unfold heapOffset; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, addr.1, decide_eq_true_eq]; omega
  · rw [addr.1]; omega
  · simp only [rangeValid, addr.2, decide_eq_true_eq]; omega
  · rw [addr.2]; omega

theorem parent_next_registers (state : MachineState) :
    (parentNextState state).getReg .x21 = state.getReg .x21 - state.getReg .x24 ∧
    (parentNextState state).getReg .x22 = state.getReg .x22 - 1536 ∧
    (parentNextState state).pc =
      (if state.getReg .x22 - 1536 = state.getReg .x9 then 6864 else 6468) ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x22 → (parentNextState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      MachineState.getReg_setReg_eq (by decide)]
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
  · intro reg n21 n22
    rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21)]

theorem parent_iteration_registers (state finished : MachineState)
    (reachable : finished ∈ support (parentIterationRun state)) :
    finished.getReg .x21 = state.getReg .x21 - state.getReg .x24 ∧
    finished.getReg .x22 = state.getReg .x22 - 1536 ∧
    finished.pc = (if state.getReg .x22 - 1536 = state.getReg .x9 then 6864 else 6468) ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x21 → reg ≠ .x22 →
      finished.getReg reg = state.getReg reg := by
  simp only [parentIterationRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨done, hdone, rfl⟩ := reachable
  have keep := (parent_calls_registers state done 0 32 hdone).2
  have next := parent_next_registers done
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.1, keep .x21 (by decide) (by decide), keep .x24 (by decide) (by decide)]
  · rw [next.2.1, keep .x22 (by decide) (by decide)]
  · rw [next.2.2.1, keep .x22 (by decide) (by decide), keep .x9 (by decide) (by decide)]
  · intro reg n10 n12 n21 n22
    rw [next.2.2.2 reg n21 n22, keep reg n10 n12]

theorem word_sub_literal (a b : Nat) (le : b ≤ a) (small : b < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) :=
  BitVec.ofNat_sub_ofNat_of_le (w := 64) a b small le

theorem parent_loop_next_invariant (state finished : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base (remaining + 1))
    (reachable : finished ∈ support (parentIterationRun state)) :
    ParentLoopInvariant finished base remaining := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have regs := parent_iteration_registers state finished reachable
  have bound := invariant.bound
  have p := invariant.pointers
  have x21 : finished.getReg .x21 = BitVec.ofNat 64 (base + 3072 * remaining + 1536) := by
    rw [regs.1, p.src, p.stride]
    show BitVec.ofNat 64 (base + 3072 * (remaining + 1) + 1536) - BitVec.ofNat 64 3072 = _
    rw [word_sub_literal _ _ (by clear * -; omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
  have sub22 : state.getReg .x22 - 1536 = BitVec.ofNat 64 (base + 1536 * remaining) := by
    rw [p.dst]
    show BitVec.ofNat 64 (base + 1536 * (remaining + 1)) - BitVec.ofNat 64 1536 = _
    rw [word_sub_literal _ _ (by clear * -; omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
  have x22 : finished.getReg .x22 = BitVec.ofNat 64 (base + 1536 * remaining) := regs.2.1.trans sub22
  have x9 : finished.getReg .x9 = BitVec.ofNat 64 base :=
    (regs.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)).trans p.heap
  have x24 : finished.getReg .x24 = 3072 :=
    (regs.2.2.2 .x24 (by decide) (by decide) (by decide) (by decide)).trans p.stride
  refine ⟨⟨x9, x21, x22, x24⟩, ?_, ?_, ?_, ?_, invariant.aligned, by omega⟩
  · rw [regs.2.2.1, sub22, p.heap]
    by_cases zero : remaining = 0
    · subst zero; simp
    · rw [if_neg, if_neg zero]
      intro same
      have := congrArg BitVec.toNat same
      rw [word_small_toNat _ (by omega), word_small_toNat _ (by omega)] at this
      omega
  · exact (regs.2.2.2 .x5 (by decide) (by decide) (by decide) (by decide)).trans invariant.r5
  · exact (regs.2.2.2 .x11 (by decide) (by decide) (by decide) (by decide)).trans invariant.r11
  · exact (regs.2.2.2 .x13 (by decide) (by decide) (by decide) (by decide)).trans invariant.r13

attribute [local irreducible] execute parentIterationRun parentCallState

/-- All 32-parent loop iterations, then the 31-parent tail. Each iteration costs
99 instructions, 323 cycles and 32 queries; the tail costs 93 instructions, 310 cycles
and 31 queries. -/
theorem commit_parents (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining) (fuel : Nat) :
    execute (submission.image .commit) (99 * remaining + 93 + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (323 * remaining + 310) (32 * remaining + 31)) := by
  induction remaining generalizing state with
  | zero =>
    have pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (692 + 3 * 0)) := by
      rw [invariant.pc]; rfl
    rw [show 99 * 0 + 93 + fuel = 3 * 31 + fuel by omega,
      commit_parent_calls state true 0 31 (by decide) pc invariant.r5 invariant.r11 invariant.r13
        (fun j _ hj => parent_call_valid_of_pointers state base 0 (31 - j) (by omega)
          invariant.pointers invariant.aligned invariant.bound)]
    simp only [commitParents, Nat.mul_zero, Nat.zero_add]
  | succ remaining ih =>
    have pc : state.pc = 6468 := by simpa using invariant.pc
    rw [show 99 * (remaining + 1) + 93 + fuel = 99 + (99 * remaining + 93 + fuel) by clear * -; omega,
      commit_parent_iteration state pc invariant.r5 invariant.r11 invariant.r13
        (fun u hu => parent_call_valid_of_pointers state base (remaining + 1) u hu
          invariant.pointers invariant.aligned invariant.bound)]
    simp only [commitParents, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (parent_loop_next_invariant state next base remaining invariant reached)]
    simp only [bind_assoc, pure_bind, charge_charge,
      show 323 + (323 * remaining + 310) = 323 * (remaining + 1) + 310 by omega,
      show 32 + (32 * remaining + 31) = 32 * (remaining + 1) + 31 by omega]

/-- The parent loop and 31-parent tail reach the root copy (`pc = 7236`) and preserve `x9`, `x26`. -/
theorem commit_parents_finished (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    finished.pc = 7236 ∧
    ∀ reg ∈ [Reg.x9, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents] at reachable
    have hregs := parent_calls_registers state finished 0 31 reachable
    refine ⟨?_, ?_⟩
    · rw [hregs.1, invariant.pc]; rfl
    · intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact hregs.2 _ (by decide) (by decide)
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (parent_loop_next_invariant state next base remaining invariant reached) rest
    have regs := parent_iteration_registers state next reached
    refine ⟨done.1, fun reg member => (done.2 reg member).trans ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact regs.2.2.2 _ (by decide) (by decide) (by decide) (by decide)

/-- Copy the root from heap node 1 into the public commitment buffer, then halt successfully. -/
theorem commit_root (state : MachineState) (pc : state.pc = 7236)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitRootCopyState state), 11, 0⟩ := by
  have nextPC : (commitRootCopyState state).pc = 7268 := by rw [commit_root_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_root_copy state pc rootValid outputValid, commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled:
`count/32` 32-leaf blocks, `count/32 - 1` 32-parent blocks + 31-parent tail, root output. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state (count / 32)
  let parents ← commitParents (commitParentsStartState leaves) (count / 32 - 1)
  return commitExitState (commitRootCopyState parents)

attribute [local irreducible] commitLeaves commitParents commitRootCopyState

/-- The heap word accesses of the root copy. -/
theorem heap_word_access (heap : Word) (base offset : Nat) (heapPointer : heap = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (offsetAligned : offset % 8 = 0) (bound : base + offset + 8 ≤ MEMORY_BYTES) :
    accessValid (heap + BitVec.ofNat 64 offset) 8 = true := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  simp only [accessValid, rangeValid, heapPointer, pointer_offset_nat base offset (by omega),
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- Exact execution of all 2^19 leaf blocks, all 2^19-1 parent blocks + 31-parent tail,
and root output for the complete tree of `2^24` leaves.
Steps: `547 * 2^19 + 12 + 99 * (2^19 - 1) + 93 + 11 = 338690065`.
Cycles: `1443 * 2^19 + 12 + 323 * (2^19 - 1) + 310 + 11 = 925892618`. -/
theorem commit_body (state : MachineState) (base : Nat)
    (leaves : CommitLeavesInvariant state (2 ^ 19))
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (leafHeapStart : state.getReg .x23 = BitVec.ofNat 64 (base + 48 * 2 ^ 24))
    (aligned : base % 8 = 0) (bound : base + 96 * 2 ^ 24 ≤ MEMORY_BYTES)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (338690065 + fuel) state true =
      (do let finished ← commitBody state (2 ^ 24)
          return ⟨.success, finished, 925892618, 5 * 2 ^ 24 - 1⟩) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  rw [show 338690065 + fuel =
    547 * 2 ^ 19 + (12 + (99 * (2 ^ 19 - 1) + 93 + (11 + fuel))) by omega,
    commit_leaves state (2 ^ 19) leaves]
  have blocks : (2 ^ 24 : Nat) / 32 = 2 ^ 19 := by norm_num
  unfold commitBody
  rw [blocks]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state (2 ^ 19) leaves hashed reached
  have start := commit_parents_start_state hashed leafDone.1
  have hashedReg (reg : Reg) (member : reg ∈ [Reg.x9, .x26, .x5, .x11, .x13]) :
      (commitParentsStartState hashed).getReg reg = state.getReg reg := by
    have notStart : reg ≠ .x6 ∧ reg ≠ .x21 ∧ reg ≠ .x22 ∧ reg ≠ .x24 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [start.2.2.2.2.2 reg notStart.1 notStart.2.1 notStart.2.2.1 notStart.2.2.2,
      leafDone.2.2 reg member]
  have x9 : (commitParentsStartState hashed).getReg .x9 = BitVec.ofNat 64 base :=
    (hashedReg .x9 (by simp)).trans heapPointer
  have hashedX23 : hashed.getReg .x23 = BitVec.ofNat 64 (base + 96 * 2 ^ 24) := by
    rw [leafDone.2.1, leafHeapStart, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
  have invariant : ParentLoopInvariant (commitParentsStartState hashed) base (2 ^ 19 - 1) := by
    refine ⟨⟨x9, ?_, ?_, start.2.1⟩, ?_, ?_, ?_, ?_, aligned, by omega⟩
    · rw [start.1, hashedX23]
      show BitVec.ofNat 64 (base + 96 * 2 ^ 24) - BitVec.ofNat 64 1536 = _
      rw [word_sub_literal _ _ (by clear * -; omega) (by decide)]
      exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
    · rw [start.2.2.1, leafDone.2.2 .x9 (by simp), heapPointer,
        show base + 1536 * (2 ^ 19 - 1) = base + 805304832 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.2.2.1, if_neg (by norm_num)]
    · exact (hashedReg .x5 (by simp)).trans leaves.r5
    · exact (hashedReg .x11 (by simp)).trans leaves.r11
    · exact (hashedReg .x13 (by simp)).trans leaves.r13
  rw [commit_parents_start hashed leafDone.1,
    commit_parents (commitParentsStartState hashed) base (2 ^ 19 - 1) invariant]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished _ base (2 ^ 19 - 1) invariant finished reachedParents
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
  rfl

end CommitGolfCandidate
