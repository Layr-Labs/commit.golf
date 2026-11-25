import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete parent loop on the gap heap (two parents per iteration), the root
call, the root output and the successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- `remaining` parent loop iterations, followed by the root call. -/
def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => do
      let answer ← World.query (.inr (parentQuery state 2))
      return parentCallState state 2 answer
  | state, remaining + 1 => do
      let next ← parentIterationRun state
      commitParents next remaining

/-- Pointer registers of the parent loop with `remaining` iterations left: the next
iteration reads pairs `2r+1` and `2r` and writes parents `2r+1` and `2r`. -/
structure ParentPointers (state : MachineState) (base remaining : Nat) : Prop where
  heap : state.getReg .x9 = BitVec.ofNat 64 base
  left : state.getReg .x21 = BitVec.ofNat 64 (base + 192*remaining)
  right : state.getReg .x22 = BitVec.ofNat 64 (base + 96*remaining)

/-- Safety and loop-control conditions of the parent loop, independent of memory. -/
structure ParentLoopInvariant (state : MachineState) (base remaining : Nat) : Prop where
  pointers : ParentPointers state base remaining
  pc : state.pc = if remaining = 0 then 4536 else 4500
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  aligned : base % 8 = 0
  bound : base + 192*remaining + 192 ≤ MEMORY_BYTES

/-- Concrete addresses of the three parent calls. -/
theorem parent_addresses (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining)
    (bound : base + 192*remaining + 192 ≤ MEMORY_BYTES) :
    (parentSource state 0).toNat = base + 192*remaining + 96 ∧
    (parentOutput state 0).toNat = base + 96*remaining + 32 ∧
    (parentSource state 1).toNat = base + 192*remaining ∧
    (parentOutput state 1).toNat = base + 96*remaining ∧
    (parentSource state 2).toNat = base + 96 ∧
    (parentOutput state 2).toNat = base + 32 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (state.getReg .x21 + BitVec.ofNat 64 96).toNat = _
    rw [pointers.left]; exact pointer_offset_nat _ 96 (by omega)
  · show (state.getReg .x22 + BitVec.ofNat 64 32).toNat = _
    rw [pointers.right]; exact pointer_offset_nat _ 32 (by omega)
  · show (state.getReg .x21 + BitVec.ofNat 64 0).toNat = _
    rw [pointers.left]; exact pointer_offset_nat _ 0 (by omega)
  · show (state.getReg .x22 + BitVec.ofNat 64 0).toNat = _
    rw [pointers.right]; exact pointer_offset_nat _ 0 (by omega)
  · show (state.getReg .x9 + BitVec.ofNat 64 96).toNat = _
    rw [pointers.heap]; exact pointer_offset_nat _ 96 (by omega)
  · show (state.getReg .x9 + BitVec.ofNat 64 32).toNat = _
    rw [pointers.heap]; exact pointer_offset_nat _ 32 (by omega)

theorem parent_call_valid_nat (state : MachineState) (j source output : Nat)
    (hs : (parentSource state j).toNat = source) (ho : (parentOutput state j).toNat = output)
    (sourceBound : source + 96 ≤ MEMORY_BYTES) (outputBound : output + 32 ≤ MEMORY_BYTES)
    (sourceAligned : source % 8 = 0) (outputAligned : output % 8 = 0) :
    ParentCallValid state j := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [rangeValid, hs, decide_eq_true_eq]; omega
  · rw [hs]; exact sourceAligned
  · simp only [rangeValid, ho, decide_eq_true_eq]; omega
  · rw [ho]; exact outputAligned

theorem parent_next_registers (state : MachineState) :
    (parentNextState state).getReg .x21 = state.getReg .x21 - 192 ∧
    (parentNextState state).getReg .x22 = state.getReg .x22 - 96 ∧
    (parentNextState state).pc =
      (if state.getReg .x22 - 96 = state.getReg .x9 then 4536 else 4500) ∧
    ∀ reg, reg ≠ .x21 → reg ≠ .x22 → (parentNextState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      MachineState.getReg_setReg_eq (by decide)]
  · rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
  · intro reg n21 n22
    rw [parentNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n22),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21)]

/-- Registers after one iteration (any oracle answers). -/
theorem parent_iteration_registers (state finished : MachineState)
    (reachable : finished ∈ support (parentIterationRun state)) :
    finished.getReg .x21 = state.getReg .x21 - 192 ∧
    finished.getReg .x22 = state.getReg .x22 - 96 ∧
    finished.pc = (if state.getReg .x22 - 96 = state.getReg .x9 then 4536 else 4500) ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x21 → reg ≠ .x22 →
      finished.getReg reg = state.getReg reg := by
  obtain ⟨a, b, rfl⟩ := parent_iteration_support state finished reachable
  have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
      (parentCallState (parentCallState state 0 a) 1 b).getReg reg = state.getReg reg := by
    rw [parent_call_register _ 1 (by decide) b reg n10 n12,
      parent_call_register _ 0 (by decide) a reg n10 n12]
  have next := parent_next_registers (parentCallState (parentCallState state 0 a) 1 b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.1, keep .x21 (by decide) (by decide)]
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
  have x21 : finished.getReg .x21 = BitVec.ofNat 64 (base + 192*remaining) := by
    rw [regs.1, p.left]
    show BitVec.ofNat 64 (base + 192*(remaining+1)) - BitVec.ofNat 64 192 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  have sub22 : state.getReg .x22 - 96 = BitVec.ofNat 64 (base + 96*remaining) := by
    rw [p.right]
    show BitVec.ofNat 64 (base + 96*(remaining+1)) - BitVec.ofNat 64 96 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  have x22 : finished.getReg .x22 = BitVec.ofNat 64 (base + 96*remaining) := regs.2.1.trans sub22
  have x9 : finished.getReg .x9 = BitVec.ofNat 64 base :=
    (regs.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)).trans p.heap
  refine ⟨⟨x9, x21, x22⟩, ?_, ?_, ?_, ?_, invariant.aligned, by omega⟩
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

attribute [local irreducible] execute parentIterationRun parentCallState

/-- All parent iterations, then the root. Each iteration costs nine instructions,
23 cycles and two queries; the root costs three instructions, ten cycles and one
query, independently of the oracle answers. -/
theorem commit_parents (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining) (fuel : Nat) :
    execute (submission.image .commit) (9 * remaining + 3 + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (23 * remaining + 10) (2 * remaining + 1)) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    have addresses := parent_addresses state base 0 invariant.pointers invariant.bound
    have bound := invariant.bound
    have aligned := invariant.aligned
    have valid : ParentCallValid state 2 :=
      parent_call_valid_nat state 2 _ _ addresses.2.2.2.2.1 addresses.2.2.2.2.2
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = BitVec.ofNat 64 (4096 + 4 * parentCallIndex 2) := by
      rw [invariant.pc]; rfl
    rw [show 9 * 0 + 3 + fuel = 3 + fuel by omega,
      commit_parent_call state 2 (by decide) pc invariant.r5 invariant.r11 invariant.r13 valid]
    simp only [commitParents, bind_assoc, pure_bind]
    try simp [Execution.charge]
  | succ remaining ih =>
    have addresses := parent_addresses state base (remaining + 1) invariant.pointers invariant.bound
    have bound := invariant.bound
    have aligned := invariant.aligned
    have first : ParentCallValid state 0 :=
      parent_call_valid_nat state 0 _ _ addresses.1 addresses.2.1
        (by omega) (by omega) (by omega) (by omega)
    have second : ParentCallValid state 1 :=
      parent_call_valid_nat state 1 _ _ addresses.2.2.1 addresses.2.2.2.1
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = 4500 := by rw [invariant.pc]; rfl
    rw [show 9 * (remaining + 1) + 3 + fuel = 9 + (9 * remaining + 3 + fuel) by omega,
      commit_parent_iteration state pc invariant.r5 invariant.r11 invariant.r13 first second]
    simp only [commitParents, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (parent_loop_next_invariant state next base remaining invariant reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The parent loop and the root reach the root copy and preserve its pointers. -/
theorem commit_parents_finished (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    finished.pc = 4548 ∧
    ∀ reg ∈ [Reg.x9, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨answer, _, rfl⟩ := reachable
    change BitVec 256 at answer
    refine ⟨?_, ?_⟩
    · rw [parent_call_pc state 2 (by decide), invariant.pc]; rfl
    · intro reg member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        exact parent_call_register state 2 (by decide) answer _ (by decide) (by decide)
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
theorem commit_root (state : MachineState) (pc : state.pc = 4548)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 113), 11, 0⟩ := by
  have copyPC : state.pc = BitVec.ofNat 64 (4096 + 4 * 113) := by rw [pc]; rfl
  have nextPC : (commitCopyState state 113).pc = 4580 := by rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 113 (Or.inr (Or.inr rfl)) copyPC rootValid
      (fun word => by simpa using outputValid word),
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled:
`count/2` leaf pairs, `count/2 - 1` parent iterations and the root, root output. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state (count / 2)
  let parents ← commitParents (commitParentsStartState leaves) (count / 2 - 1)
  return commitExitState (commitCopyState parents 113)

attribute [local irreducible] commitLeaves commitParents commitCopyState

/-- The heap word accesses of the root copy. -/
theorem heap_word_access (heap : Word) (base offset : Nat) (heapPointer : heap = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (offsetAligned : offset % 8 = 0) (bound : base + offset + 8 ≤ MEMORY_BYTES) :
    accessValid (heap + BitVec.ofNat 64 offset) 8 = true := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  simp only [accessValid, rangeValid, heapPointer, pointer_offset_nat base offset (by omega),
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- Exact execution of all leaf pairs, all parents, the root and root output for the
actual tree of `2^24` leaves. Safety conditions constrain addresses only; the theorem
covers every message and salt. -/
theorem commit_body (state : MachineState) (base : Nat)
    (leaves : CommitLeavesInvariant state (2 ^ 23))
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base + 96 * 2 ^ 24 ≤ MEMORY_BYTES)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (27 * 2 ^ 24 + 22 + fuel) state true =
      (do let finished ← commitBody state (2 ^ 24)
          return ⟨.success, finished, 62 * 2 ^ 24 + 15, 5 * 2 ^ 24 - 1⟩) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  rw [show 27 * 2 ^ 24 + 22 + fuel =
    45 * 2 ^ 23 + (17 + (9 * (2 ^ 23 - 1) + 3 + (11 + fuel))) by omega,
    commit_leaves state (2 ^ 23) leaves]
  have half : (2 ^ 24 : Nat) / 2 = 2 ^ 23 := by norm_num
  unfold commitBody
  rw [half]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state (2 ^ 23) leaves hashed reached
  have start := commit_parents_start_state hashed leafDone.1
  have hashedReg (reg : Reg) (member : reg ∈ [Reg.x9, .x26, .x5, .x11, .x13]) :
      (commitParentsStartState hashed).getReg reg = state.getReg reg := by
    have notStart : reg ≠ .x6 ∧ reg ≠ .x21 ∧ reg ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [start.2.2.2.2 reg notStart.1 notStart.2.1 notStart.2.2, leafDone.2 reg member]
  have x9 : (commitParentsStartState hashed).getReg .x9 = BitVec.ofNat 64 base :=
    (hashedReg .x9 (by simp)).trans heapPointer
  have invariant : ParentLoopInvariant (commitParentsStartState hashed) base (2 ^ 23 - 1) := by
    refine ⟨⟨x9, ?_, ?_⟩, ?_, ?_, ?_, ?_, aligned, by omega⟩
    · rw [start.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 192 * (2 ^ 23 - 1) = base + 1610612544 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 96 * (2 ^ 23 - 1) = base + 805306272 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.2.1, if_neg (by norm_num)]
    · exact (hashedReg .x5 (by simp)).trans leaves.r5
    · exact (hashedReg .x11 (by simp)).trans leaves.r11
    · exact (hashedReg .x13 (by simp)).trans leaves.r13
  rw [commit_parents_start hashed leafDone.1,
    commit_parents (commitParentsStartState hashed) base (2 ^ 23 - 1) invariant]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished _ base (2 ^ 23 - 1) invariant finished reachedParents
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
