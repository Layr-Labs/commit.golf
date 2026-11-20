import CommitGolfCandidate.CommitParents
import CommitGolfCandidate.CommitLoop

/-! The complete parent loop, followed by root output and successful HALT. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def commitParents : MachineState → Nat → OracleComp World MachineState
  | state, 0 => pure state
  | state, remaining + 1 => do
      let answer ← World.query (.inr (commitParentQuery state))
      commitParents (commitParentNextState (commitParentState state answer)) remaining

/-- The parent heap is readable/writable for every node still to be computed. -/
def ParentBuffers (base : Word) (remaining : Nat) : Prop :=
  ∀ node, 0 < node → node ≤ remaining →
    rangeValid (base + (BitVec.ofNat 64 node <<< 6)) 64 = true ∧
    rangeValid (base + (BitVec.ofNat 64 node <<< 5)) 32 = true ∧
    (base + (BitVec.ofNat 64 node <<< 6)).toNat % 8 = 0 ∧
    (base + (BitVec.ofNat 64 node <<< 5)).toNat % 8 = 0

theorem commit_parent_step_counter (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).getReg .x20 = state.getReg .x20 - 1 := by
  change (commitParentState state answer).getReg .x20 - 1 = _
  rw [commit_parent_register state answer .x20 (by simp)]

theorem commit_parent_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (member : reg ∈ [Reg.x9, .x19, .x21, .x26]) :
    (commitParentNextState (commitParentState state answer)).getReg reg = state.getReg reg := by
  have not20 : Reg.x20 ≠ reg := by intro h; subst reg; simp at member
  rw [commitParentNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ not20]
  apply commit_parent_register
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
  tauto

theorem commit_parent_step_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentNextState (commitParentState state answer)).pc =
      if state.getReg .x20 - 1 = 0 then 4408 else 4368 := by
  change (if (commitParentState state answer).getReg .x20 - 1 = 0 then 4408 else 4368) = _
  rw [commit_parent_register state answer .x20 (by simp)]

attribute [local irreducible] execute commitParentState commitParentNextState

/-- All internal nodes are processed in descending heap order. Each costs ten
instructions, seventeen cycles, and one query, independently of oracle answers. -/
theorem commit_parents (state : MachineState) (remaining : Nat) (bounded : remaining < 2 ^ 24)
    (pc : 0 < remaining → state.pc = 4368)
    (counter : state.getReg .x20 = BitVec.ofNat 64 remaining)
    (buffers : ParentBuffers (state.getReg .x9) remaining) (fuel : Nat) :
    execute (submission.image .commit) (10 * remaining + fuel) state true =
      (do let finished ← commitParents state remaining
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge (17 * remaining) remaining) := by
  induction remaining generalizing state with
  | zero => simp [commitParents, Execution.charge]
  | succ remaining ih =>
    have current := buffers (remaining + 1) (by omega) (by omega)
    rw [← counter] at current
    have nextCounter (answer : BitVec 256) :
        (commitParentNextState (commitParentState state answer)).getReg .x20 = BitVec.ofNat 64 remaining := by
      rw [commit_parent_step_counter, counter]
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < remaining) :
        (commitParentNextState (commitParentState state answer)).pc = 4368 := by
      rw [commit_parent_step_pc]
      apply if_neg
      rw [← commit_parent_step_counter state answer, nextCounter]
      intro zero
      have equal := congrArg BitVec.toNat zero
      change remaining % 18446744073709551616 = 0 at equal
      omega
    have nextBuffers (answer : BitVec 256) :
        ParentBuffers ((commitParentNextState (commitParentState state answer)).getReg .x9) remaining := by
      rw [commit_parent_step_register state answer .x9 (by simp)]
      exact fun node positive bound => buffers node positive (by omega)
    rw [show 10 * (remaining + 1) + fuel = 10 + (10 * remaining + fuel) by omega,
      commit_parent state (pc (by omega)) current.1 current.2.1 current.2.2.1 current.2.2.2]
    simp only [commitParents, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    change BitVec 256 at answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer) (nextBuffers answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem commit_parents_finished (state : MachineState) (remaining : Nat)
    (bounded : remaining < 2 ^ 24)
    (counter : state.getReg .x20 = BitVec.ofNat 64 remaining)
    (finished : MachineState) (reachable : finished ∈ support (commitParents state remaining)) :
    (0 < remaining → finished.pc = 4408) ∧
    ∀ reg ∈ [Reg.x9, .x19, .x21, .x26], finished.getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitParents, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by omega, fun _ _ => rfl⟩
  | succ remaining ih =>
    simp only [commitParents, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have nextCounter : (commitParentNextState (commitParentState state answer)).getReg .x20 =
        BitVec.ofNat 64 remaining := by
      rw [commit_parent_step_counter, counter]
      change BitVec.ofNat 64 (remaining + 1) - BitVec.ofNat 64 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (remaining + 1) 1 (by decide) (by omega)]
      congr 1
    have done := ih _ (by omega) nextCounter reached
    refine ⟨?_, fun reg member => (done.2 reg member).trans (commit_parent_step_register state answer reg member)⟩
    intro _
    by_cases empty : remaining = 0
    · subst remaining
      simp only [commitParents, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_parent_step_pc, counter]
      rfl
    · exact done.1 (Nat.pos_of_ne_zero empty)

/-- Initialize the descending internal-node counter. -/
def commitParentsStartState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getReg .x19 - 1)).setPC
    (if state.getReg .x19 - 1 = 0 then 4408 else 4368)

theorem commit_parents_start (state : MachineState) (pc : state.pc = 4360) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentsStartState state) true
          return result.charge 2 0) := by
  let next := (state.setReg .x20 (state.getReg .x19 - 1)).setPC 4364
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x20 .x19 4095)) := by
    apply commit_fetch _ 66 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.BEQ .x20 .x0 44)) := by
    apply commit_fetch _ 67 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x20 .x19 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have s1 : ordinaryStep next (.base (.BEQ .x20 .x0 44)) = some (commitParentsStartState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, commitParentsStartState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0, execute_ordinary_step _ _ _ _ _ _ f1 s1]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 4448

theorem commit_exit (state : MachineState) (pc : state.pc = 4440) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 4444
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 86 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 87 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 88 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, MachineState.getReg]
  have s1 : ordinaryStep next (.base (.ADDI .x10 .x0 0)) = some (commitExitState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, commitExitState, MachineState.getReg, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, instructionCycles, bind_assoc, pure_bind]
  simp [commitExitState, MachineState.getReg, MachineState.setReg, MachineState.setPC, Execution.charge]

/-- Copy the root from heap node one into the public commitment buffer, then halt
successfully. This costs eleven cycles and makes no oracle queries. -/
theorem commit_root (state : MachineState) (pc : state.pc = 4408)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 78), 11, 0⟩ := by
  have nextPC : (commitCopyState state 78).pc = 4440 := by rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 78 (Or.inr (Or.inr rfl)) pc rootValid outputValid,
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state count
  let parents ← commitParents (commitParentsStartState leaves) (count - 1)
  return commitExitState (commitCopyState parents 78)

attribute [local irreducible] commitLeaves commitParents commitCopyState

set_option maxRecDepth 4096 in
/-- Exact execution of all leaves, all internal nodes, and root output. Safety
conditions constrain addresses only; the theorem covers every message and salt. -/
theorem commit_body (state : MachineState) (count : Nat)
    (positive : 2 ≤ count) (bounded : count ≤ 2 ^ 24)
    (leaves : CommitLeavesInvariant state count)
    (total : state.getReg .x19 = BitVec.ofNat 64 count)
    (parents : ParentBuffers (state.getReg .x9) (count - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (113 * count + 3 + fuel) state true =
      (do let finished ← commitBody state count
          return ⟨.success, finished, 176 * count - 4, 9 * count - 1⟩) := by
  rw [show 113 * count + 3 + fuel =
    103 * count + (2 + (10 * (count - 1) + (11 + fuel))) by omega,
    commit_leaves state count leaves]
  simp only [commitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state count leaves hashed reached
  let ready := commitParentsStartState hashed
  have readyRegister (reg : Reg) (notCounter : Reg.x20 ≠ reg) :
      ready.getReg reg = hashed.getReg reg := by
    dsimp only [ready]
    rw [commitParentsStartState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ notCounter]
  have readyCount : ready.getReg .x20 = BitVec.ofNat 64 (count - 1) := by
    change hashed.getReg .x19 - 1 = _
    rw [leafDone.2 .x19 (by simp), total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have readyPC : 0 < count - 1 → ready.pc = 4368 := by
    intro _
    change (if hashed.getReg .x19 - 1 = 0 then 4408 else 4368) = _
    rw [leafDone.2 .x19 (by simp), total]
    apply if_neg
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 ≠ 0
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count - 1) % 18446744073709551616 = 0 at equal
    omega
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by decide)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by decide)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]; exact parents
  rw [commit_parents_start hashed leafDone.1,
    commit_parents ready (count - 1) (by omega) readyPC readyCount readyBuffers]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega) readyCount finished reachedParents
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]; exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]; exact outputValid
  rw [commit_root finished (parentDone.1 (by omega)) root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega

end CommitGolfCandidate
