import CommitGolfCandidate.HeapLatch

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
    commit_copy state 79 rfl pc rootValid outputValid,
    commit_exit _ nextPC]
  rfl

/-- State distribution of the full tree-building phase, after salts are sampled. -/
def commitBody (state : MachineState) (count : Nat) : OracleComp World MachineState := do
  let leaves ← commitLeaves state count
  let parents ← commitParents (commitParentsStartState leaves) (count - 1)
  return commitExitState (commitCopyState parents 79)

end CommitGolfCandidate
