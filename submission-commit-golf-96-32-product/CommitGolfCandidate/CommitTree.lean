import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete parent loop on the gap heap (two parents per iteration) down to the
cap level, the 64-call chain over the cap pairs, the commitment output and the
successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- `remaining` parent loop iterations; the loop stops at the cap level. -/
def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← parentIterationRun state
      commitParents next remaining

/-- Pointer registers of the parent loop with `remaining` iterations left: with
`p = r + 63`, the next iteration reads pairs `2p+1` and `2p` and writes parents `2p+1`
and `2p`. The loop stops at x22 = x7 = base + 96*63, after parent 128. -/
structure ParentPointers (state : MachineState) (base remaining : Nat) : Prop where
  heap : state.getReg .x9 = BitVec.ofNat 64 base
  left : state.getReg .x21 = BitVec.ofNat 64 (base + 192*remaining + 12096)
  right : state.getReg .x22 = BitVec.ofNat 64 (base + 96*remaining + 6048)
  stop : state.getReg .x7 = BitVec.ofNat 64 (base + 6048)

/-- Safety and loop-control conditions of the parent loop, independent of memory. -/
structure ParentLoopInvariant (state : MachineState) (base remaining : Nat) : Prop where
  pointers : ParentPointers state base remaining
  pc : state.pc = if remaining = 0 then 4560 else 4524
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  aligned : base % 8 = 0
  bound : base + 192*remaining + 12096 + 192 ≤ MEMORY_BYTES

/-- Concrete addresses of the two parent calls of an iteration. -/
theorem parent_addresses (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining)
    (bound : base + 192*remaining + 12096 + 192 ≤ MEMORY_BYTES) :
    (parentSource state 0).toNat = base + 192*remaining + 12096 + 96 ∧
    (parentOutput state 0).toNat = base + 96*remaining + 6048 + 32 ∧
    (parentSource state 1).toNat = base + 192*remaining + 12096 ∧
    (parentOutput state 1).toNat = base + 96*remaining + 6048 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (state.getReg .x21 + BitVec.ofNat 64 96).toNat = _
    rw [pointers.left]; exact pointer_offset_nat _ 96 (by omega)
  · show (state.getReg .x22 + BitVec.ofNat 64 32).toNat = _
    rw [pointers.right]; exact pointer_offset_nat _ 32 (by omega)
  · show (state.getReg .x21 + BitVec.ofNat 64 0).toNat = _
    rw [pointers.left]; exact pointer_offset_nat _ 0 (by omega)
  · show (state.getReg .x22 + BitVec.ofNat 64 0).toNat = _
    rw [pointers.right]; exact pointer_offset_nat _ 0 (by omega)

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
      (if state.getReg .x22 - 96 = state.getReg .x7 then 4560 else 4524) ∧
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
    finished.pc = (if state.getReg .x22 - 96 = state.getReg .x7 then 4560 else 4524) ∧
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
  · rw [next.2.2.1, keep .x22 (by decide) (by decide), keep .x7 (by decide) (by decide)]
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
  have x21 : finished.getReg .x21 = BitVec.ofNat 64 (base + 192*remaining + 12096) := by
    rw [regs.1, p.left]
    show BitVec.ofNat 64 (base + 192*(remaining+1) + 12096) - BitVec.ofNat 64 192 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  have sub22 : state.getReg .x22 - 96 = BitVec.ofNat 64 (base + 96*remaining + 6048) := by
    rw [p.right]
    show BitVec.ofNat 64 (base + 96*(remaining+1) + 6048) - BitVec.ofNat 64 96 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  have x22 : finished.getReg .x22 = BitVec.ofNat 64 (base + 96*remaining + 6048) := regs.2.1.trans sub22
  have x9 : finished.getReg .x9 = BitVec.ofNat 64 base :=
    (regs.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)).trans p.heap
  have x7 : finished.getReg .x7 = BitVec.ofNat 64 (base + 6048) :=
    (regs.2.2.2 .x7 (by decide) (by decide) (by decide) (by decide)).trans p.stop
  refine ⟨⟨x9, x21, x22, x7⟩, ?_, ?_, ?_, ?_, invariant.aligned, by omega⟩
  · rw [regs.2.2.1, sub22, p.stop]
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

theorem charge_zero (result : Execution) : result.charge 0 0 = result := by
  cases result; simp [Execution.charge]

/-- All parent iterations above the cap. Each iteration costs nine instructions,
23 cycles and two queries, independently of the oracle answers. -/
theorem commit_parents (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining) (fuel : Nat) :
    execute (submission.image .commit) (9 * remaining + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (23 * remaining) (2 * remaining)) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, pure_bind, Nat.mul_zero, Nat.zero_add, charge_zero, bind_pure]
  | succ remaining ih =>
    have addresses := parent_addresses state base (remaining + 1) invariant.pointers invariant.bound
    have bound := invariant.bound
    have aligned := invariant.aligned
    have first : ParentCallValid state 0 :=
      parent_call_valid_nat state 0 _ _ addresses.1 addresses.2.1
        (by omega) (by omega) (by omega) (by omega)
    have second : ParentCallValid state 1 :=
      parent_call_valid_nat state 1 _ _ addresses.2.2.1 addresses.2.2.2
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = 4524 := by rw [invariant.pc]; rfl
    rw [show 9 * (remaining + 1) + fuel = 9 + (9 * remaining + fuel) by omega,
      commit_parent_iteration state pc invariant.r5 invariant.r11 invariant.r13 first second]
    simp only [commitParents, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (parent_loop_next_invariant state next base remaining invariant reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- The parent loop ends at the cap chain with its pointers at the cap level. -/
theorem commit_parents_finished (state : MachineState) (base remaining : Nat)
    (invariant : ParentLoopInvariant state base remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    ParentLoopInvariant finished base 0 ∧
    ∀ reg ∈ [Reg.x9, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨invariant, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (parent_loop_next_invariant state next base remaining invariant reached) rest
    have regs := parent_iteration_registers state next reached
    refine ⟨done.1, fun reg member => (done.2 reg member).trans ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact regs.2.2.2 _ (by decide) (by decide) (by decide) (by decide)

/-- `remaining` iterations of the chain over the cap pairs. -/
def commitChain : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let next ← chainIterationRun state
      commitChain next remaining

/-- Chain loop with `remaining` cap pairs left: x21 points at the gap holding the
current chain state, directly below cap pair `64 - remaining`. -/
structure ChainLoopInvariant (state : MachineState) (base remaining : Nat) : Prop where
  pointer : state.getReg .x21 = BitVec.ofNat 64 (base + 12256 - 96*remaining)
  counter : state.getReg .x20 = BitVec.ofNat 64 remaining
  pc : state.pc = if remaining = 0 then 4600 else 4576
  r5 : state.getReg .x5 = 0
  r11 : state.getReg .x11 = 96
  r13 : state.getReg .x13 = 0
  aligned : base % 8 = 0
  inside : remaining ≤ 64
  bound : base + 12288 ≤ MEMORY_BYTES

theorem chain_addresses (state : MachineState) (base remaining : Nat)
    (invariant : ChainLoopInvariant state base (remaining+1)) :
    (parentSource state 2).toNat = base + 12256 - 96*(remaining+1) ∧
    (parentOutput state 2).toNat = base + 12256 - 96*remaining := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have bound := invariant.bound
  have inside := invariant.inside
  constructor
  · show (state.getReg .x21 + BitVec.ofNat 64 0).toNat = _
    rw [invariant.pointer]; exact pointer_offset_nat _ 0 (by omega)
  · show (state.getReg .x21 + BitVec.ofNat 64 96).toNat = _
    rw [invariant.pointer, pointer_offset_nat _ 96 (by omega)]
    omega

theorem chain_next_registers (state : MachineState) :
    (chainNextState state).getReg .x21 = state.getReg .x21 + 96 ∧
    (chainNextState state).getReg .x20 = state.getReg .x20 - 1 ∧
    (chainNextState state).pc = (if state.getReg .x20 - 1 = 0 then 4600 else 4576) ∧
    ∀ reg, reg ≠ .x20 → reg ≠ .x21 → (chainNextState state).getReg reg = state.getReg reg := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [chainNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      MachineState.getReg_setReg_eq (by decide)]
  · rw [chainNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
  · intro reg n20 n21
    rw [chainNextState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n20),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm n21)]

theorem chain_iteration_registers (state finished : MachineState)
    (reachable : finished ∈ support (chainIterationRun state)) :
    finished.getReg .x21 = state.getReg .x21 + 96 ∧
    finished.getReg .x20 = state.getReg .x20 - 1 ∧
    finished.pc = (if state.getReg .x20 - 1 = 0 then 4600 else 4576) ∧
    ∀ reg, reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x20 → reg ≠ .x21 →
      finished.getReg reg = state.getReg reg := by
  obtain ⟨a, rfl⟩ := chain_iteration_support state finished reachable
  have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
      (parentCallState state 2 a).getReg reg = state.getReg reg :=
    parent_call_register state 2 (by decide) a reg n10 n12
  have next := chain_next_registers (parentCallState state 2 a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.1, keep .x21 (by decide) (by decide)]
  · rw [next.2.1, keep .x20 (by decide) (by decide)]
  · rw [next.2.2.1, keep .x20 (by decide) (by decide)]
  · intro reg n10 n12 n20 n21
    rw [next.2.2.2 reg n20 n21, keep reg n10 n12]

theorem chain_loop_next_invariant (state finished : MachineState) (base remaining : Nat)
    (invariant : ChainLoopInvariant state base (remaining + 1))
    (reachable : finished ∈ support (chainIterationRun state)) :
    ChainLoopInvariant finished base remaining := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have regs := chain_iteration_registers state finished reachable
  have bound := invariant.bound
  have inside := invariant.inside
  have counter : state.getReg .x20 - 1 = BitVec.ofNat 64 remaining := by
    rw [invariant.counter]
    show BitVec.ofNat 64 (remaining+1) - BitVec.ofNat 64 1 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1
  refine ⟨?_, regs.2.1.trans counter, ?_, ?_, ?_, ?_, invariant.aligned, by omega, bound⟩
  · rw [regs.1, invariant.pointer]
    show BitVec.ofNat 64 (base + 12256 - 96*(remaining+1)) + BitVec.ofNat 64 96 = _
    rw [BitVec.ofNat_add_ofNat]
    congr 1
    omega
  · rw [regs.2.2.1, counter]
    by_cases zero : remaining = 0
    · subst zero
      simp
    · rw [if_neg, if_neg zero]
      intro same
      have := congrArg BitVec.toNat same
      rw [word_small_toNat _ (by omega)] at this
      simp at this
      omega
  · exact (regs.2.2.2 .x5 (by decide) (by decide) (by decide) (by decide)).trans invariant.r5
  · exact (regs.2.2.2 .x11 (by decide) (by decide) (by decide) (by decide)).trans invariant.r11
  · exact (regs.2.2.2 .x13 (by decide) (by decide) (by decide) (by decide)).trans invariant.r13

attribute [local irreducible] chainIterationRun

/-- All chain iterations: six instructions, 13 cycles and one query each. -/
theorem commit_chain (state : MachineState) (base remaining : Nat)
    (invariant : ChainLoopInvariant state base remaining) (fuel : Nat) :
    execute (submission.image .commit) (6 * remaining + fuel) state true =
      (do let finished ← commitChain state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (13 * remaining) remaining) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    simp only [commitChain, pure_bind, Nat.mul_zero, Nat.zero_add, charge_zero, bind_pure]
  | succ remaining ih =>
    have addresses := chain_addresses state base remaining invariant
    have bound := invariant.bound
    have aligned := invariant.aligned
    have inside := invariant.inside
    have valid : ParentCallValid state 2 :=
      parent_call_valid_nat state 2 _ _ addresses.1 addresses.2
        (by omega) (by omega) (by omega) (by omega)
    have pc : state.pc = 4576 := by rw [invariant.pc]; rfl
    rw [show 6 * (remaining + 1) + fuel = 6 + (6 * remaining + fuel) by omega,
      commit_chain_iteration state pc invariant.r5 invariant.r11 invariant.r13 valid]
    simp only [commitChain, bind_assoc]
    apply bind_congr_of_forall_mem_support
    intro next reached
    rw [ih next (chain_loop_next_invariant state next base remaining invariant reached)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem commit_chain_finished (state : MachineState) (base remaining : Nat)
    (invariant : ChainLoopInvariant state base remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitChain state remaining)) :
    ChainLoopInvariant finished base 0 ∧
    ∀ reg ∈ [Reg.x9, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitChain, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨invariant, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitChain, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    have done := ih next (chain_loop_next_invariant state next base remaining invariant reached) rest
    have regs := chain_iteration_registers state next reached
    refine ⟨done.1, fun reg member => (done.2 reg member).trans ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      exact regs.2.2.2 _ (by decide) (by decide) (by decide) (by decide)

/-- Copy the final chain state into the public commitment buffer, then halt
successfully. This costs eleven cycles and makes no oracle queries. -/
theorem commit_root (state : MachineState) (pc : state.pc = 4600)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 126), 11, 0⟩ := by
  have copyPC : state.pc = BitVec.ofNat 64 (4096 + 4 * 126) := by rw [pc]; rfl
  have nextPC : (commitCopyState state 126).pc = 4632 := by rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 126 (Or.inr (Or.inr rfl)) copyPC (fun word => by simpa using rootValid word)
      (fun word => by simpa using outputValid word),
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled:
`count/2` leaf pairs, `count/2 - 64` parent iterations down to the cap, the 64-call
cap chain and the commitment output. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state (count / 2)
  let parents ← commitParents (commitParentsStartState leaves) (count / 2 - 64)
  let chained ← commitChain (capStartState parents) 64
  return commitExitState (commitCopyState chained 126)

attribute [local irreducible] commitLeaves commitParents commitChain commitCopyState

/-- The heap word accesses of the commitment copy. -/
theorem heap_word_access (heap : Word) (base offset : Nat) (heapPointer : heap = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (offsetAligned : offset % 8 = 0) (bound : base + offset + 8 ≤ MEMORY_BYTES) :
    accessValid (heap + BitVec.ofNat 64 offset) 8 = true := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  simp only [accessValid, rangeValid, heapPointer, pointer_offset_nat base offset (by omega),
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

/-- Chain loop facts at the cap start, for any state reached by the parent loop. -/
theorem cap_start_invariant (parents : MachineState) (base : Nat)
    (invariant : ParentLoopInvariant parents base 0) (bound : base + 12288 ≤ MEMORY_BYTES) :
    ChainLoopInvariant (capStartState parents) base 64 := by
  have pc : parents.pc = 4560 := by rw [invariant.pc]; rfl
  have start := cap_start_state parents pc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, invariant.aligned, by omega, bound⟩
  · rw [start.1, invariant.pointers.right]
    show BitVec.ofNat 64 _ + BitVec.ofNat 64 64 = _
    rw [BitVec.ofNat_add_ofNat]
    apply congrArg (BitVec.ofNat 64)
    rw [Nat.add_sub_assoc (by norm_num : 96*64 ≤ 12256)]
  · rw [start.2.1]; rfl
  · rw [start.2.2.1]; rfl
  · rw [start.2.2.2.2 .x5 (by decide) (by decide)]; exact invariant.r5
  · rw [start.2.2.2.2 .x11 (by decide) (by decide)]; exact invariant.r11
  · rw [start.2.2.2.2 .x13 (by decide) (by decide)]; exact invariant.r13

set_option maxHeartbeats 1600000 in
/-- Exact execution of all leaf pairs, all parents above the cap, the cap chain and
the commitment output for the actual tree of `2^24` leaves. Safety conditions
constrain addresses only; the theorem covers every message and salt. -/
theorem commit_body (state : MachineState) (base : Nat)
    (leaves : CommitLeavesInvariant state (2 ^ 23))
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (aligned : base % 8 = 0) (bound : base + 96 * 2 ^ 24 ≤ MEMORY_BYTES)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (27 * 2 ^ 24 - 154 + fuel) state true =
      (do let finished ← commitBody state (2 ^ 24)
          return ⟨.success, finished, 62 * 2 ^ 24 - 602, 5 * 2 ^ 24 - 64⟩) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  rw [show 27 * 2 ^ 24 - 154 + fuel =
    45 * 2 ^ 23 + (23 + (9 * (2 ^ 23 - 64) + (4 + (6 * 64 + (11 + fuel))))) by omega,
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
    have notStart : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x21 ∧ reg ≠ .x22 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [start.2.2.2.2.2 reg notStart.1 notStart.2.1 notStart.2.2.1 notStart.2.2.2,
      leafDone.2 reg member]
  have x9 : (commitParentsStartState hashed).getReg .x9 = BitVec.ofNat 64 base :=
    (hashedReg .x9 (by simp)).trans heapPointer
  have invariant : ParentLoopInvariant (commitParentsStartState hashed) base (2 ^ 23 - 64) := by
    refine ⟨⟨x9, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, aligned, by omega⟩
    · rw [start.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 192 * (2 ^ 23 - 64) + 12096 = base + 1610612544 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.1, (leafDone.2 .x9 (by simp)), heapPointer,
        show base + 96 * (2 ^ 23 - 64) + 6048 = base + 805306272 by norm_num, BitVec.ofNat_add]
      rfl
    · rw [start.2.2.1, (leafDone.2 .x9 (by simp)), heapPointer, BitVec.ofNat_add]
      rfl
    · rw [start.2.2.2.1, if_neg (by norm_num)]
    · exact (hashedReg .x5 (by simp)).trans leaves.r5
    · exact (hashedReg .x11 (by simp)).trans leaves.r11
    · exact (hashedReg .x13 (by simp)).trans leaves.r13
  rw [commit_parents_start hashed leafDone.1,
    commit_parents (commitParentsStartState hashed) base (2 ^ 23 - 64) invariant]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro parents reachedParents
  have parentDone := commit_parents_finished _ base (2 ^ 23 - 64) invariant parents reachedParents
  have capPC : parents.pc = 4560 := by rw [parentDone.1.pc]; rfl
  have chainStart := cap_start_invariant parents base parentDone.1 (by omega)
  rw [commit_cap_start parents capPC, commit_chain (capStartState parents) base 64 chainStart]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro chained reachedChain
  have chainDone := commit_chain_finished _ base 64 chainStart chained reachedChain
  have capStart := cap_start_state parents capPC
  have root : ∀ word : Fin 4,
      accessValid (chained.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    have := word.isLt
    have pointer : chained.getReg .x21 = BitVec.ofNat 64 (base + 12256) := by
      rw [chainDone.1.pointer]; rfl
    exact heap_word_access _ (base + 12256) _ pointer (by omega) (by omega) (by omega)
  have output : ∀ word : Fin 4,
      accessValid (chained.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [chainDone.2 .x26 (by simp), capStart.2.2.2.2 .x26 (by decide) (by decide),
      parentDone.2 .x26 (by simp), hashedReg .x26 (by simp)]
    exact outputValid
  have donePC : chained.pc = 4600 := by rw [chainDone.1.pc]; rfl
  rw [commit_root chained donePC root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  norm_num

end CommitGolfCandidate
