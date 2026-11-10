import CommitGolfCandidate.PointerStart

/-! The full pointer-based parent phase and successful commitment return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def commitExitState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 4452

theorem commit_exit (state : MachineState) (pc : state.pc = 4444) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      pure ⟨.success, commitExitState state, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC 4448
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x5 .x0 1)) := by
    apply commit_fetch _ 87 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.ADDI .x10 .x0 0)) := by
    apply commit_fetch _ 88 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) (commitExitState state) = some (.base .ECALL) := by
    apply commit_fetch _ 89 _ (by decide) rfl; rfl
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
theorem commit_root (state : MachineState) (pc : state.pc = 4412)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 79), 11, 0⟩ := by
  have nextPC : (commitCopyState state 79).pc = 4444 := by rw [commit_copy_pc, pc]; rfl
  rw [show 11 + fuel = 8 + (3 + fuel) by omega,
    commit_copy state 79 (Or.inr (Or.inr rfl)) pc rootValid outputValid,
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state count
  let parents ← commitParents (commitParentsStartState leaves) (count - 1)
  return commitExitState (commitCopyState parents 79)

attribute [local irreducible] commitLeaves commitParents commitCopyState

private theorem load_pc_frame (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc+4) := by
  cases destination <;> rfl

private theorem store_pc_frame (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc+4) := rfl

private theorem root_copy_pc_frame (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 79 = (commitCopyState state 79).setPC (pc+32) := by
  rw [commit_copy_expansion, commit_copy_expansion]
  simp only [show (79 : Nat) ≠ 46 by decide, show (79 : Nat) ≠ 55 by decide,
    ite_false, ite_true, List.foldl, load_pc_frame, store_pc_frame]
  simp only [BitVec.add_assoc]
  rfl

/-- The positive loop's terminal jump and unchanged root-copy/halt cost twelve
cycles. The final state is independent of the pre-jump program counter. -/
private theorem commit_positive_root (state : MachineState) (pc : state.pc = 4404)
    (rootValid : ∀ word : Fin 4,
      accessValid (state.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (12 + fuel) state true =
      pure ⟨.success, commitExitState (commitCopyState state 79), 12, 0⟩ := by
  rw [show 12+fuel = 1+(11+fuel) by omega, pointer_parent_exit state pc,
    commit_root (state.setPC 4412) rfl rootValid outputValid]
  simp only [pure_bind, Execution.charge]
  rw [root_copy_pc_frame]
  unfold commitExitState
  rfl

set_option maxRecDepth 4096 in
/-- Exact execution, including inherited syscall readiness and the once-only
setup and terminal jump. Address conditions cover every message and salt. -/
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
    execute (submission.image .commit) (44 * count + 14 + fuel) state true =
      (do let finished ← commitBody state count
          return ⟨.success, finished, 107 * count + 7, 9 * count - 1⟩) := by
  rw [show 44 * count + 14 + fuel =
    40 * count + (6 + (4 * (count - 1) + (12 + fuel))) by omega,
    commit_leaves state count leaves]
  simp only [commitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro hashed reached
  have leafDone := commit_leaves_finished state count leaves hashed reached
  have leafInvariant := commit_leaves_final_invariant state count leaves hashed reached
  let ready := commitParentsStartState hashed
  have readyRegister (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      ready.getReg reg = hashed.getReg reg := by
    apply commit_parents_start_register hashed reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have residual : hashed.getReg .x19 - 1 = BitVec.ofNat 64 (count - 1) := by
    rw [leafDone.2 .x19 (by simp), total]
    change BitVec.ofNat 64 count - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) count 1 (by decide) (by omega)]
  have nonempty : hashed.getReg .x19 - 1 ≠ 0 := by
    rw [residual]
    intro zero
    have equal := congrArg BitVec.toNat zero
    change (count - 1) % 18446744073709551616 = 0 at equal
    omega
  have readyPointers : ParentPointerInvariant ready (count-1) :=
    commit_parents_start_pointers hashed (count-1) nonempty residual
  have readyPC : 0 < count-1 → ready.pc = 4388 :=
    fun _ => commit_parents_start_pc hashed nonempty
  have readyHeap : ready.getReg .x9 = state.getReg .x9 :=
    (readyRegister .x9 (by simp)).trans (leafDone.2 .x9 (by simp))
  have readyOutput : ready.getReg .x26 = state.getReg .x26 :=
    (readyRegister .x26 (by simp)).trans (leafDone.2 .x26 (by simp))
  have readyBuffers : ParentBuffers (ready.getReg .x9) (count - 1) := by
    rw [readyHeap]; exact parents
  rw [commit_parents_start hashed leafDone.1 nonempty,
    commit_parents ready (count - 1) (by omega) readyPC readyPointers
      (commit_parents_start_constants hashed leafInvariant.oracleReady) readyBuffers]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (count - 1) (by omega) readyPointers finished reachedParents
  have root : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [parentDone.2 .x9 (by simp), readyHeap]; exact rootValid
  have output : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [parentDone.2 .x26 (by simp), readyOutput]; exact outputValid
  rw [commit_positive_root finished (parentDone.1 (by omega)) root output]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1
  congr 1 <;> omega

end CommitGolfCandidate
