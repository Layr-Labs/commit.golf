import CommitGolfCandidate.S6ParentMemory
import CommitGolfCandidate.S3Exec

/-! The parent sweep on the actual interpreter. Seven setup instructions (PC 1015304) end in a jump
to the second parent of the loop body; the body holds 256 unrolled parents of four instructions
(`ecall; sh x0,30(x12); addi x10,x10,-64; addi x12,x12,-32`, PC 1015332 + 16 j) and the branch
`bne x12,x9` (PC 1019428); after the last pass the jump at PC 1019432 goes to the root copy at
PC 4412. A parent costs eleven cycles and one compression query; the sweep makes a first pass of
255 parents and 16,383 passes of 256: 4,194,303 parents, for every sequence of replies. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Arithmetic helpers -/

private theorem s6_pc_next (pc : Word) (start k target : Nat) (h : pc = BitVec.ofNat 64 start)
    (sum : start + k = target) : pc + BitVec.ofNat 64 k = BitVec.ofNat 64 target := by
  rw [h, ← sum, BitVec.ofNat_add]

private theorem s6_pointer_nat (register : Word) (address : Nat)
    (value : register = BitVec.ofNat 64 address) (bounded : address ≤ MEMORY_BYTES) :
    register.toNat = address := by
  rw [value, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  dsimp [MEMORY_BYTES] at bounded
  omega

private theorem charge_charge (result : Execution) (a b c d : Nat) :
    (result.charge a b).charge c d = result.charge (c + a) (d + b) := by
  simp only [Execution.charge, Nat.add_assoc]

/-! ### One parent -/

/-- Syscall arguments and pointers at a parent: node `node`'s children at x10, its slot at x12. -/
structure S6ParentState (state : MachineState) (heap node : Nat) : Prop where
  ready : S6CompressionReady state
  pointers : S6SweepPointers state heap node

/-- The state only depends on registers x5, x9..x13. -/
theorem S6ParentState.congr {state : MachineState} {heap node : Nat}
    (invariant : S6ParentState state heap node) (other : MachineState)
    (registers : ∀ reg, other.getReg reg = state.getReg reg) : S6ParentState other heap node :=
  ⟨⟨(registers .x5).trans invariant.ready.1, (registers .x11).trans invariant.ready.2.1,
      (registers .x13).trans invariant.ready.2.2⟩,
    ⟨(registers .x9).trans invariant.pointers.base, (registers .x10).trans invariant.pointers.input,
      (registers .x12).trans invariant.pointers.output⟩⟩

theorem s6_parent_result_state (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (heap node : Nat) (invariant : S6ParentState state heap (node + 1)) :
    S6ParentState (s6ParentResult state answer) heap node := by
  have kept (reg : Reg) (h10 : reg ≠ .x10 := by decide) (h12 : reg ≠ .x12 := by decide) :=
    s6_parent_result_register state answer reg h10 h12
  exact ⟨⟨(kept .x5).trans invariant.ready.1, (kept .x11).trans invariant.ready.2.1,
    (kept .x13).trans invariant.ready.2.2⟩,
    s6_parent_result_pointers state answer heap node invariant.pointers⟩

set_option maxHeartbeats 8000000 in
/-- Parent `j` of the loop body: compression query on the children of `node + 1`, reply at its
slot, truncating store, pointer steps. Four instructions, eleven cycles, one query. -/
theorem s6_parent_execute (j : Nat) (hj : j < 256) (state : MachineState) (heap node : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1015332 + 16 * j))
    (invariant : S6ParentState state heap (node + 1))
    (aligned : heap % 8 = 0) (bound : heap + 64 * (node + 1) + 64 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let next ← s6Parent state
          let result ← execute (submission.image .commit) fuel next true
          return result.charge 11 1) ∧
    ∀ answer, (s6ParentResult state answer).pc = BitVec.ofNat 64 (1015332 + 16 * (j + 1)) := by
  have call := s6_compression_call (submission.image .commit) state (3 + fuel) true
    (s6_image_parent j 0 hj (by decide) state (by rw [pc, Nat.mul_zero, Nat.add_zero]))
    invariant.ready
    (by rw [s6_pointer_nat _ _ invariant.pointers.input (by omega)]; omega)
    (by rw [s6_pointer_nat _ _ invariant.pointers.output (by omega)]; omega)
    (by rw [s6_pointer_nat _ _ invariant.pointers.input (by omega)]; omega)
    (by rw [s6_pointer_nat _ _ invariant.pointers.output (by omega)]; omega)
  have repliedPC (answer : BitVec COMPRESSION_OUTPUT_LENGTH) :
      (s6ParentReply state answer).pc = BitVec.ofNat 64 (1015332 + 16 * j + 4 * 1) := by
    rw [s6_parent_reply_pc]
    exact s6_pc_next _ _ 4 _ pc (by omega)
  have step (answer : BitVec COMPRESSION_OUTPUT_LENGTH) :=
    s3_straight_execute (submission.image .commit) s6ParentStepInstructions 3
      (1015332 + 16 * j + 4 * 1) (s6ParentReply state answer) fuel true rfl (repliedPC answer)
      (by decide)
      (fun k bound current currentPC => by
        have fetched := s6_image_parent j (1 + k) hj (by omega) current
          (by rw [currentPC]; congr 1; omega)
        interval_cases k <;> exact fetched)
      (fun k bound => by
        interval_cases k
        · apply s3_half_access_valid _ _ (heap + 32 * (node + 1)) 30
            ((s6_parent_reply_register state answer .x12).trans invariant.pointers.output) rfl
            (by omega) (by decide) (by omega)
        · rfl
        · rfl)
  refine ⟨?_, fun answer => ?_⟩
  · rw [show 4 + fuel = 1 + (3 + fuel) by omega, call]
    simp only [s6Parent, bind_assoc, pure_bind]
    refine bind_congr fun answer => ?_
    rw [(step answer).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · have done : (s6ParentResult state answer).pc =
        BitVec.ofNat 64 (1015332 + 16 * j + 4 * 1 + 4 * 3) := (step answer).2
    rw [done]
    exact congrArg (BitVec.ofNat 64) (by omega)

/-! ### Runs, passes and the sweep -/

/-- Parents `j, j+1, ..., j+count-1` of the loop body, for nodes `node + count` down to
`node + 1`. -/
theorem s6_parent_run_execute (count : Nat) :
    ∀ (j : Nat) (state : MachineState) (heap node : Nat),
    j + count ≤ 256 →
    state.pc = BitVec.ofNat 64 (1015332 + 16 * j) → S6ParentState state heap (node + count) →
    heap % 8 = 0 → heap + 64 * (node + count) + 64 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (4 * count + fuel) state true =
      (do let swept ← s6ParentRun state count
          let result ← execute (submission.image .commit) fuel swept true
          return result.charge (11 * count) count) ∧
    ∀ swept ∈ support (s6ParentRun state count),
      swept.pc = BitVec.ofNat 64 (1015332 + 16 * (j + count)) ∧ S6ParentState swept heap node ∧
      ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → swept.getReg reg = state.getReg reg := by
  induction count with
  | zero =>
    intro j state heap node _ pc invariant _ _ fuel
    refine ⟨by simp [s6ParentRun, Execution.charge], ?_⟩
    intro swept reachable
    simp only [s6ParentRun, support_pure, Set.mem_singleton_iff] at reachable
    subst reachable
    exact ⟨by rw [Nat.add_zero]; exact pc, invariant, fun _ _ _ => rfl⟩
  | succ count ih =>
    intro j state heap node inside pc invariant aligned bound fuel
    have parent := s6_parent_execute j (by omega) state heap (node + count)
      pc invariant aligned (by omega) (4 * count + fuel)
    have continued (answer : BitVec COMPRESSION_OUTPUT_LENGTH) :=
      ih (j + 1) (s6ParentResult state answer) heap node (by omega) (parent.2 answer)
        (s6_parent_result_state state answer heap (node + count) invariant) aligned (by omega) fuel
    constructor
    · rw [show 4 * (count + 1) + fuel = 4 + (4 * count + fuel) by omega, parent.1]
      simp only [s6ParentRun, bind_assoc]
      refine bind_congr_of_forall_mem_support _ fun reached reachable => ?_
      obtain ⟨answer, rfl⟩ := s6_parent_support state reached reachable
      rw [(continued answer).1]
      simp only [bind_assoc, pure_bind]
      refine bind_congr fun swept => ?_
      refine bind_congr fun result => ?_
      simp [Execution.charge]
      omega
    · intro swept reachable
      simp only [s6ParentRun, mem_support_bind_iff] at reachable
      obtain ⟨reached, reachedParent, rest⟩ := reachable
      obtain ⟨answer, rfl⟩ := s6_parent_support state reached reachedParent
      have tail := (continued answer).2 swept rest
      refine ⟨by rw [tail.1, show j + 1 + count = j + (count + 1) by omega], tail.2.1,
        fun reg h10 h12 => (tail.2.2 reg h10 h12).trans
          (s6_parent_result_register state answer reg h10 h12)⟩

/-- The loop branch: back to the body start while nodes remain, else to the exit jump. -/
theorem s6_branch_pc (state : MachineState) (heap node : Nat)
    (pc : state.pc = BitVec.ofNat 64 1019428) (invariant : S6ParentState state heap node)
    (bound : heap + 32 * node < 2 ^ 64) :
    (execInstrBr state s6ParentBranch).pc =
      BitVec.ofNat 64 (if node = 0 then 1019432 else 1015332) := by
  by_cases zero : node = 0
  · rw [if_pos zero]
    have same : (state.getReg .x12 != state.getReg .x9) = false := by
      rw [invariant.pointers.output, invariant.pointers.base, zero, Nat.mul_zero, Nat.add_zero]
      simp
    simp only [s6ParentBranch, execInstrBr, same, Bool.false_eq_true, ↓reduceIte, pc]
    rfl
  · rw [if_neg zero]
    have different : BitVec.ofNat 64 (heap + 32 * node) ≠ BitVec.ofNat 64 heap := by
      intro equal
      have := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat] at this
      omega
    have unequal : (state.getReg .x12 != state.getReg .x9) = true := by
      rw [invariant.pointers.output, invariant.pointers.base]
      simpa using different
    simp only [s6ParentBranch, execInstrBr, unequal, ↓reduceIte, pc]
    rfl

set_option maxHeartbeats 8000000 in
/-- A pass from parent `256 - count` of the body: `count` parents and the branch. -/
theorem s6_parent_pass_execute (count : Nat) (positive : 0 < count) (inside : count ≤ 256)
    (state : MachineState) (heap node : Nat)
    (pc : state.pc = BitVec.ofNat 64 (1015332 + 16 * (256 - count)))
    (invariant : S6ParentState state heap (node + count))
    (aligned : heap % 8 = 0) (bound : heap + 64 * (node + count) + 64 ≤ MEMORY_BYTES) (fuel : Nat) :
    execute (submission.image .commit) (4 * count + 1 + fuel) state true =
      (do let next ← s6ParentPass state count
          let result ← execute (submission.image .commit) fuel next true
          return result.charge (11 * count + 1) count) ∧
    ∀ next ∈ support (s6ParentPass state count),
      next.pc = BitVec.ofNat 64 (if node = 0 then 1019432 else 1015332) ∧
      S6ParentState next heap node ∧
      ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → next.getReg reg = state.getReg reg := by
  have run := s6_parent_run_execute count (256 - count) state heap node (by omega) pc invariant
    aligned bound (1 + fuel)
  have branch (swept : MachineState) (reached : swept ∈ support (s6ParentRun state count)) :
      execute (submission.image .commit) (fuel + 1) swept true =
        (do let result ← execute (submission.image .commit) fuel
              (execInstrBr swept s6ParentBranch) true
            return result.charge 1 0) :=
    execute_ordinary_step (submission.image .commit) (.base s6ParentBranch) swept _ fuel true
      (s6_image_parent_branch swept (by
        rw [(run.2 swept reached).1]
        exact congrArg (BitVec.ofNat 64) (by omega))) rfl
  constructor
  · rw [show 4 * count + 1 + fuel = 4 * count + (1 + fuel) by omega, run.1]
    simp only [s6ParentPass, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun swept reached => ?_
    rw [Nat.add_comm 1 fuel, branch swept reached]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    simp [Execution.charge]
    omega
  · intro next reachable
    simp only [s6ParentPass, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨swept, reached, rfl⟩ := reachable
    have known := run.2 swept reached
    have kept (reg : Reg) : (execInstrBr swept s6ParentBranch).getReg reg = swept.getReg reg :=
      s6_parent_branch_register swept reg
    refine ⟨?_, known.2.1.congr _ kept, fun reg h10 h12 => (kept reg).trans (known.2.2 reg h10 h12)⟩
    exact s6_branch_pc swept heap node (by rw [known.1]; exact congrArg (BitVec.ofNat 64) (by omega))
      known.2.1 (by dsimp [MEMORY_BYTES] at bound; omega)

/-- `passes` full passes of 256 parents from the body start, for nodes `256 * passes` down to 1. -/
theorem s6_parent_passes_execute (passes : Nat) :
    ∀ (state : MachineState) (heap : Nat), 0 < passes →
    state.pc = BitVec.ofNat 64 1015332 → S6ParentState state heap (256 * passes) →
    heap % 8 = 0 → heap + 64 * (256 * passes) + 64 ≤ MEMORY_BYTES → ∀ fuel : Nat,
    execute (submission.image .commit) (1025 * passes + fuel) state true =
      (do let swept ← s6ParentPasses state passes
          let result ← execute (submission.image .commit) fuel swept true
          return result.charge (2817 * passes) (256 * passes)) ∧
    ∀ swept ∈ support (s6ParentPasses state passes),
      swept.pc = BitVec.ofNat 64 1019432 ∧ S6ParentState swept heap 0 ∧
      ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → swept.getReg reg = state.getReg reg := by
  induction passes with
  | zero => intro _ _ positive; omega
  | succ passes ih =>
    intro state heap _ pc invariant aligned bound fuel
    have pass (more : Nat) := s6_parent_pass_execute 256 (by decide) (le_refl _) state heap
      (256 * passes) (pc.trans (by norm_num))
      (by rw [show 256 * passes + 256 = 256 * (passes + 1) by omega]; exact invariant) aligned (by omega) more
    rcases Nat.eq_zero_or_pos passes with rfl | positive
    · constructor
      · rw [show 1025 * (0 + 1) + fuel = 4 * 256 + 1 + fuel by omega, (pass fuel).1]
        simp only [s6ParentPasses, bind_assoc, pure_bind]
      · intro swept reachable
        simp only [s6ParentPasses, bind_pure] at reachable
        have known := (pass 0).2 swept reachable
        exact ⟨by rw [known.1, if_pos (by decide)], known.2.1, known.2.2⟩
    · have continued (next : MachineState) (reached : next ∈ support (s6ParentPass state 256)) :=
        ih next heap positive
          (by rw [((pass 0).2 next reached).1, if_neg (by omega)])
          ((pass 0).2 next reached).2.1 aligned (by omega) fuel
      constructor
      · rw [show 1025 * (passes + 1) + fuel = 4 * 256 + 1 + (1025 * passes + fuel) by omega,
          (pass (1025 * passes + fuel)).1]
        simp only [s6ParentPasses, bind_assoc]
        refine bind_congr_of_forall_mem_support _ fun next reached => ?_
        rw [(continued next reached).1]
        simp only [bind_assoc, pure_bind]
        refine bind_congr fun swept => ?_
        refine bind_congr fun result => ?_
        simp [Execution.charge]
        omega
      · intro swept reachable
        rw [s6ParentPasses] at reachable
        simp only [mem_support_bind_iff] at reachable
        obtain ⟨next, reached, remaining⟩ := reachable
        have tail := (continued next reached).2 swept remaining
        exact ⟨tail.1, tail.2.1, fun reg h10 h12 => (tail.2.2 reg h10 h12).trans
          (((pass 0).2 next reached).2.2 reg h10 h12)⟩

theorem s6_parent_exit_pc (state : MachineState) (pc : state.pc = BitVec.ofNat 64 1019432) :
    (execInstrBr state s6ParentExit).pc = 4412 := by
  rw [s6ParentExit, s6_jal_zero]
  show state.pc + signExtend21 (BitVec.ofNat 21 1082132) = _
  rw [pc]
  decide

set_option maxHeartbeats 16000000 in
/-- **The parent sweep** from PC 1015304: setup, a first pass of 255 parents, 16,383 passes
of 256 and the jump to the root copy: `7 + 4 * 4194303 + 16384 + 1` instructions,
`7 + 11 * 4194303 + 16384 + 1` cycles, 4,194,303 compression queries. -/
theorem s6_parents_execute (state : MachineState) (heap : Nat) (fuel : Nat)
    (pc : state.pc = BitVec.ofNat 64 1015304)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap) (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2^28))
    (selector : state.getReg .x5 = 0) (aligned : heap % 8 = 0) (bound : heap + 2^28 ≤ MEMORY_BYTES) :
    execute (submission.image .commit) (7 + 4 * 4194303 + 16384 + 1 + fuel) state true =
      (do let finished ← s6Parents state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (7 + 11 * 4194303 + 16384 + 1) 4194303) ∧
    ∀ finished ∈ support (s6Parents state), finished.pc = 4412 ∧ finished.getReg .x9 = state.getReg .x9 ∧
      finished.getReg .x26 = state.getReg .x26 := by
  have setup := s3_straight_execute (submission.image .commit) (s6ParentSetupInstructions.take 6) 6
    1015304 state ((4 * 255 + 1 + (1025 * 16383 + (1 + fuel))) + 1) true rfl pc (by decide)
    (fun k bound current currentPC => by
      have fetched := s6_image_parent_setup k (by omega) current currentPC
      interval_cases k <;> exact fetched)
    (fun k bound => by interval_cases k <;> rfl)
  have setupPC : ((s6ParentSetupInstructions.take 6).foldl execInstrBr state).pc =
      BitVec.ofNat 64 (1015304 + 4 * 6) := setup.2
  have jump : execute (submission.image .commit) ((4 * 255 + 1 + (1025 * 16383 + (1 + fuel))) + 1)
      ((s6ParentSetupInstructions.take 6).foldl execInstrBr state) true =
      (do let result ← execute (submission.image .commit) (4 * 255 + 1 + (1025 * 16383 + (1 + fuel)))
            (s6ParentSetup state) true
          return result.charge 1 0) :=
    execute_ordinary_step (submission.image .commit) (.base (.JAL .x0 20)) _ (s6ParentSetup state) _ true
      (s6_image_parent_setup 6 (by decide) _ setupPC) rfl
  have ready : S6ParentState (s6ParentSetup state) heap (2 ^ 22 - 1) :=
    ⟨⟨(s6_parent_setup_register state .x5 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans selector, rfl, rfl⟩, s6_parent_setup_pointers state heap base top⟩
  have startPC : (s6ParentSetup state).pc = BitVec.ofNat 64 (1015332 + 16 * (256 - 255)) := by
    show ((s6ParentSetupInstructions.take 6).foldl execInstrBr state).pc + signExtend21 20 = _
    rw [setupPC]
    rfl
  have count : (256 * 16383 + 255 : Nat) = 2 ^ 22 - 1 := by norm_num
  have first := s6_parent_pass_execute 255 (by decide) (by decide) (s6ParentSetup state) heap
    (256 * 16383) startPC (by rw [count]; exact ready) aligned
    (by dsimp [MEMORY_BYTES] at bound ⊢; omega) (1025 * 16383 + (1 + fuel))
  have rest (next : MachineState) (reached : next ∈ support (s6ParentPass (s6ParentSetup state) 255)) :=
    s6_parent_passes_execute 16383 next heap (by decide)
      (by rw [((first.2 next reached).1), if_neg (by decide)]) (first.2 next reached).2.1 aligned
      (by dsimp [MEMORY_BYTES] at bound ⊢; omega) (1 + fuel)
  constructor
  · rw [show 7 + 4 * 4194303 + 16384 + 1 + fuel =
        6 + ((4 * 255 + 1 + (1025 * 16383 + (1 + fuel))) + 1) by omega, setup.1, jump]
    simp only [bind_assoc, pure_bind]
    rw [first.1]
    simp only [s6Parents, bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun next reached => ?_
    rw [(rest next reached).1]
    simp only [bind_assoc, pure_bind]
    refine bind_congr_of_forall_mem_support _ fun swept sweptReached => ?_
    rw [Nat.add_comm 1 fuel, execute_ordinary_step (submission.image .commit) (.base s6ParentExit)
      swept _ fuel true (s6_image_parent_exit swept ((rest next reached).2 swept sweptReached).1) rfl]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun result => ?_
    have exitCycles : instructionCycles (.base s6ParentExit) = 1 := rfl
    rw [exitCycles]
    simp only [charge_charge]
  · intro finished reachable
    simp only [s6Parents, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨next, reached, swept, sweptReached, rfl⟩ := reachable
    have known := (rest next reached).2 swept sweptReached
    have reachable : execInstrBr swept s6ParentExit ∈ support (s6Parents state) := by
      simp only [s6Parents, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
      exact ⟨next, reached, swept, sweptReached, rfl⟩
    exact ⟨s6_parent_exit_pc swept known.1,
      s6_parents_register state _ reachable .x9 (by decide),
      s6_parents_register state _ reachable .x26 (by decide)⟩

end CommitGolfCandidate
