import CommitGolfCandidate.FusedPairLoop

/-! The peeled first parent leaves an even residual. A zero residual exits at
PC4404; a completed pair loop exits at PC4344. Each pays exactly one root jump. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] execute pointerParentState

def PeeledBranchFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    state.pc = 4400 → fetch image state = some (.base (.BNE .x12 .x9 8108))

def ParentExitFetched (image : Image) : Prop :=
  ∀ state : MachineState,
    (state.pc = 4344 → fetch image state = some (.base (.JAL .x0 68))) ∧
    (state.pc = 4404 → fetch image state = some (.base (.JAL .x0 8)))

theorem fused_peel_branch (image : Image) (fetched : PeeledBranchFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * pairs < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * pairs)) (fuel : Nat) :
    execute image (1 + fuel) (state.setPC 4400) true =
      (do let result ← execute image fuel
            (state.setPC (if pairs = 0 then 4404 else 4316)) true
          return result.charge 1 0) := by
  have done : state.getReg .x12 = state.getReg .x9 ↔ pairs = 0 := by
    rw [pointers.2, parent_pointer_done_iff _ (2 * pairs) bounded]
    omega
  change state.regs .x12 = state.regs .x9 ↔ pairs = 0 at done
  have stepped : ordinaryStep (state.setPC 4400) (.base (.BNE .x12 .x9 8108)) =
      some (state.setPC (if pairs = 0 then 4404 else 4316)) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      MachineState.getReg, MachineState.getReg_setPC, MachineState.setPC, done]
    split <;> simp_all
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
    (fetched (state.setPC 4400) rfl) stepped]
  rfl

theorem fused_parent_exit (image : Image) (fetched : ParentExitFetched image)
    (state : MachineState) (start : Word) (location : start = 4344 ∨ start = 4404)
    (fuel : Nat) :
    execute image (1 + fuel) (state.setPC start) true =
      (do let result ← execute image fuel (state.setPC 4412) true
          return result.charge 1 0) := by
  rcases location with rfl | rfl
  · have stepped : ordinaryStep (state.setPC 4344) (.base (.JAL .x0 68)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4344)).1 rfl) stepped]
    rfl
  · have stepped : ordinaryStep (state.setPC 4404) (.base (.JAL .x0 8)) =
        some (state.setPC 4412) := by
      simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
        MachineState.setReg, MachineState.setPC]
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _
      ((fetched (state.setPC 4404)).2 rfl) stepped]
    rfl

/-- Pair execution and its exit jump, with the peeled-only path handled directly. -/
theorem fused_parent_remainder (image : Image)
    (firstFetched : ParentTripleFetched image 4316)
    (secondFetched : ParentTripleFetched image 4328)
    (branchFetched : PairedBranchFetched image) (exitFetched : ParentExitFetched image)
    (state : MachineState) (pairs : Nat) (bounded : 2 * pairs < 2 ^ 24)
    (pointers : ParentPointerInvariant state (2 * pairs))
    (constants : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (buffers : ParentBuffers (state.getReg .x9) (2 * pairs)) (fuel : Nat) :
    execute image (7 * pairs + 1 + fuel)
      (state.setPC (if pairs = 0 then 4404 else 4316)) true =
      (do let finished ← commitParents state (2 * pairs)
          let result ← execute image fuel (finished.setPC 4412) true
          return result.charge (21 * pairs + 1) (2 * pairs)) := by
  by_cases empty : pairs = 0
  · subst pairs
    simp only [Nat.mul_zero, Nat.zero_add, ite_true, commitParents, pure_bind]
    exact fused_parent_exit image exitFetched state 4404 (Or.inr rfl) fuel
  · have loop := fused_pairs image firstFetched secondFetched branchFetched state pairs
      bounded pointers constants buffers (1 + fuel)
    simp only [if_neg empty] at loop ⊢
    rw [show 7 * pairs + 1 + fuel = 7 * pairs + (1 + fuel) by omega, loop]
    apply bind_congr_of_forall_mem_support
    intro finished _
    rw [fused_parent_exit image exitFetched finished 4344 (Or.inl rfl) fuel]
    simp [Execution.charge, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end CommitGolfCandidate
